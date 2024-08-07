/** @file inifcns_trans.cpp
 *
 *  Implementation of transcendental (and hyperbolic) functions. */

/*
 *  ginacsym Copyright (C) 1999-2008 Johannes Gutenberg University Mainz, Germany
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 */


#include "inifcns.h"
#include "ex.h"
#include "constant.h"
#include "infinity.h"
#include "numeric.h"
#include "mul.h"
#include "power.h"
#include "operators.h"
#include "relational.h"
#include "symbol.h"
#include "pseries.h"
#include "utils.h"
#include "add.h"

#include <vector>
#include <stdexcept>
#include <string>
#include <memory>
#include <unordered_set>

namespace ginacsym {


/* In Sage all the arc trig functions are printed with "arc" instead
   of "a" at the beginning.   This is for consistency with other
   computer algebra systems.   These print methods are registered
   below with each of the corresponding inverse trig function. */


//////////
// exponential function
//////////

static ex exp_evalf(const ex & x)
{
    if (is_exactly_a<numeric>(x))
        return exp(ex_to<numeric>(x));

    return exp(x).hold();
}

static ex exp_eval(const ex & x)
{
    // exp(0) -> 1
    if (x.is_zero()) {
        return _ex1;
    }

    // handle infinity
    // This needs to be before the other tests below, since multiplying
    // infinity with other values throws runtime_errors
    // exp(oo) -> oo
    // exp(-oo) -> 0
    // exp(UnsignedInfinity) -> error
    if (is_exactly_a<infinity>(x)) {
        const infinity& xinf = ex_to<infinity>(x);
        if (xinf.info(info_flags::positive))
            return Infinity;
        if (xinf.info(info_flags::negative))
            return _ex0;
        // x is UnsignedInfinity
        throw (std::runtime_error("exp_eval(): exp^(unsigned_infinity) encountered"));
    }

    bool has_pi = false;
    std::function<bool (const ex&)> has_pi_and_py =
        [&](const ex & the_ex) -> bool
    {
        if (is_exactly_a<constant>(the_ex)
            and ex_to<constant>(the_ex) == Pi)
            has_pi = true;
        for (size_t i=0; i<the_ex.nops(); ++i)
            if (has_pi_and_py(the_ex.op(i)))
                return true;
        return false;
    };

    ex x_red;
    if (has_pi_and_py(x)) { // true if x contains Pi and Python objects
        // like I. To make this check should be faster
        // than the following

        ex coef_pi = x.coeff(Pi,1).expand();
        ex rem = _ex0;
        if (is_exactly_a<add>(coef_pi)) {
            for (size_t i=0; i < coef_pi.nops(); i++) {
                if ((coef_pi.op(i) / (_ex2 * I)).info(info_flags::integer))
                    rem += Pi * coef_pi.op(i);
            }
        }
        else if ((coef_pi / (_ex2 * I)).info(info_flags::integer))
            rem = Pi * coef_pi;
        x_red = (x - rem).expand();


        ex res1 = sin(x_red/I);
        ex res2 = cos(x_red/I);
        if (((not is_exactly_a<function>(res1))
             or (not is_ex_the_function(res1, sin)))
            and ((not is_exactly_a<function>(res2))
                 or (not is_ex_the_function(res2, cos))))
            return I*res1 + res2;
    }
    else
        x_red = x;

    if (is_exactly_a<function>(x_red)) {
        const ex& arg = x_red.op(0);
        // exp(log(x)) -> x
        if (is_ex_the_function(x_red, log))
            return arg;
        // exp(asinh(num)) etc.
        // see https://en.wikipedia.org/wiki/Hyperbolic_functions#Inverse_functions_as_logarithms
        if (is_exactly_a<numeric>(arg)) {
            // exp(asinh(x)) -> x + sqrt(x^2 + 1)
            if (is_ex_the_function(x_red, asinh))
                return arg + sqrt(power(arg, _ex2) + _ex1);
            // exp(acosh(x)) -> x + sqrt(x^2 - 1)
            if (is_ex_the_function(x_red, acosh))
                return arg + sqrt(power(arg, _ex2) - _ex1);
            // exp(atanh(x)) -> sqrt((1 + x)/(1 - x))
            if (is_ex_the_function(x_red, atanh))
                return sqrt((_ex1 + arg) / (_ex1 - x));
            // exp(acoth(x)) -> sqrt((x + 1)/(x - 1))
            if (is_ex_the_function(x_red, acoth))
                return sqrt((arg + _ex1) / (arg - _ex1));
            // exp(asech(x)) -> 1/x + sqrt(1 - x^2)/x
            if (is_ex_the_function(x_red, asech))
                return (_ex1/arg +
                        sqrt(_ex1 - power(arg, _ex2))/arg);
            // exp(acsch(x)) -> 1/x + sqrt(1 + 1/x^2)
            if (is_ex_the_function(x_red, acsch))
                return (_ex1/arg +
                        sqrt(_ex1 + _ex1/power(arg, _ex2)));
        }
    }

    static std::unordered_set<unsigned int> funcs = { log_SERIAL::serial,
                                                     asinh_SERIAL::serial, acosh_SERIAL::serial,
                                                     atanh_SERIAL::serial, acoth_SERIAL::serial,
                                                     asech_SERIAL::serial, acsch_SERIAL::serial };

    if (is_exactly_a<mul>(x_red)) {
        // Loop through factors finding and marking the function.
        // Don't proceed if more than one function found.
        bool function_seen = false, applicable = false;
        size_t func_idx;
        for (size_t i=0; i<x_red.nops(); ++i) {
            const ex& fac = x_red.op(i);
            if (is_exactly_a<function>(fac)
                and funcs.find(ex_to<function>(fac).get_serial()) != funcs.end()) {
                if (function_seen)
                { applicable = false; break; }
                function_seen = applicable = true;
                func_idx = i;
            }
        }
        if (applicable) {
            ex c = _ex1;
            for (size_t i=0; i<x_red.nops(); ++i)
                if (i != func_idx)
                    c *= x_red.op(i);
            const ex& fac = x_red.op(func_idx);
            const ex& arg = fac.op(0);
            // exp(c*log(ex)) -> ex^c
            if (is_ex_the_function(fac, log))
                return power(arg, c);
            // exp(c*asinh(ex)) etc.
            // see https://en.wikipedia.org/wiki/Hyperbolic_functions#Inverse_functions_as_logarithms
            // exp(asinh(x)) -> x + sqrt(x^2 + 1)
            if (is_ex_the_function(fac, asinh))
                return power(arg + sqrt(power(arg, _ex2) + 1),
                             c);
            // exp(acosh(x)) -> x + sqrt(x^2 - 1)
            if (is_ex_the_function(fac, acosh))
                return power(arg + sqrt(power(arg, _ex2) - 1),
                             c);
            // exp(atanh(x)) -> sqrt((1 + x)/(1 - x))
            if (is_ex_the_function(fac, atanh))
                return power((_ex1 + arg) / (_ex1 - arg), c/2);
            // exp(acoth(x)) -> sqrt((x + 1)/(x - 1))
            if (is_ex_the_function(fac, acoth))
                return power((arg + _ex1) / (arg - _ex1), c/2);
            // exp(asech(x)) -> 1/x + sqrt(1 - x^2)/x
            if (is_ex_the_function(fac, asech))
                return power(_ex1/arg +
                                 sqrt(_ex1 - power(arg, _ex2))/arg,
                             c);
            // exp(acsch(x)) -> 1/x + sqrt(1 + 1/x^2)
            if (is_ex_the_function(fac, acsch))
                return power(_ex1/arg +
                                 sqrt(_ex1 + _ex1/power(arg, _ex2)),
                             c);
        }
    }

    // exp(float) -> float
    if (x.info(info_flags::numeric) && !x.info(info_flags::crational))
        return exp(ex_to<numeric>(x));

    return exp(x_red).hold();
}

static ex exp_expand(const ex & arg, unsigned options)
{
    ex exp_arg;
    if (options & expand_options::expand_function_args)
        exp_arg = arg.expand(options);
    else
        exp_arg=arg;

    if ((options & expand_options::expand_transcendental)
        && is_exactly_a<add>(exp_arg)) {
        exvector prodseq;
        prodseq.reserve(exp_arg.nops());
        for (const_iterator i = exp_arg.begin(); i != exp_arg.end(); ++i)
            prodseq.push_back(exp(*i));

        return dynallocate<mul>(prodseq).setflag(status_flags::expanded);
    }

    return exp(exp_arg).hold();
}

static ex exp_power(const ex & x, const ex & a)
{
    /*
     * The power law (e^x)^a=e^(x*a) is used in two cases:
     * a) a is an integer and x may be complex;
     * b) both x and a are reals.
     * c) a is real
     * Negative a is excluded to keep automatic simplifications like exp(x)/exp(x)=1.
     */
    if (/*a.info(info_flags::nonnegative)
        && */(a.info(info_flags::integer) || (x.info(info_flags::real) && a.info(info_flags::real))))
        return exp(x*a);
    else if(x.info(info_flags::real))
        return exp(x*a);
//    else if (a.info(info_flags::negative)
//             && (a.info(info_flags::integer) || (x.info(info_flags::real) && a.info(info_flags::real))))
//        return power(exp(-x*a), _ex_1).hold();

    return power(exp(x), a).hold();
}

static bool exp_info(const ex & x, unsigned inf)
{
    switch (inf) {
    case info_flags::expanded:
    case info_flags::real:
        return x.info(inf);
    case info_flags::positive:
    case info_flags::nonnegative:
        return x.info(info_flags::real);
    default:
        return false;
    }
}

static ex exp_deriv(const ex & x, unsigned deriv_param)
{
    GINAC_ASSERT(deriv_param==0);

    // d/dx exp(x) -> exp(x)
    return exp(x);
}


static ex exp_real_part(const ex & x)
{
    return exp(ginacsym::real_part(x))*cos(ginacsym::imag_part(x));
}

static ex exp_imag_part(const ex & x)
{
    return exp(ginacsym::real_part(x))*sin(ginacsym::imag_part(x));
}

static ex exp_conjugate(const ex & x)
{
    // conjugate(exp(x))==exp(conjugate(x))
    return exp(x.conjugate());
}

//static void exp_print(const ex & arg, const print_context & c)
//{
//    c.s << "exp\\left(";arg.print(c);c.s<<"\\right)";
//}


static void exp_print_latex(const ex & arg, const print_context & c)
{
    c.s << "{e^{";arg.print(c);c.s<<"}}";
}


REGISTER_FUNCTION(exp,
                       evalf_func(exp_evalf).
                       eval_func(exp_eval).
                       expand_func(exp_expand).
                       power_func(exp_power).
                       info_func(exp_info).
                       derivative_func(exp_deriv).
                       real_part_func(exp_real_part).
                       imag_part_func(exp_imag_part).
                       conjugate_func(exp_conjugate).
                       print_func<print_latex>(exp_print_latex));

//////////
// natural logarithm
//////////

static ex log_evalf(const ex & x)
{
    if (is_exactly_a<numeric>(x))
        return log(ex_to<numeric>(x));

    return log(x).hold();
}

static ex log_eval(const ex & x)
{
    if (x.info(info_flags::numeric)) {
        if (x.is_zero())         // log(0) -> infinity
            //throw(pole_error("log_eval(): log(0)",0));
            return -Infinity;
        if (x.info(info_flags::rational) && x.info(info_flags::negative))
            return (log(-x)+I*Pi);
        if (x.is_equal(_ex1))  // log(1) -> 0
            return _ex0;
        if (x.is_equal(I))       // log(I) -> Pi*I/2
            return (Pi*I*_ex1_2);
        if (x.is_equal(-I))      // log(-I) -> -Pi*I/2
            return (Pi*I*_ex_1_2);

        // log(float) -> float
        if (!x.info(info_flags::crational))
            return log(ex_to<numeric>(x));
    }

    // log(exp(t)) -> t (if -Pi < t.imag() <= Pi):
    if (is_ex_the_function(x, exp)) {
        const ex &t = x.op(0);
        if (t.info(info_flags::real))
            return t;
    }

    // log(oo) -> oo
    if (is_a<infinity>(x)) {
        return Infinity;
    }

    return log(x).hold();
}


static ex log_expand(const ex & arg, unsigned options)
{
    if ((options & expand_options::expand_transcendental)
        && is_exactly_a<mul>(arg) && !arg.info(info_flags::indefinite)) {
        exvector sumseq;
        exvector prodseq;
        sumseq.reserve(arg.nops());
        prodseq.reserve(arg.nops());
        bool possign=true;

        // searching for positive/negative factors
        for (const_iterator i = arg.begin(); i != arg.end(); ++i) {
            ex e;
            if (options & expand_options::expand_function_args)
                e=i->expand(options);
            else
                e=*i;
            if (e.info(info_flags::positive))
                sumseq.push_back(log(e));
            else if (e.info(info_flags::negative)) {
                sumseq.push_back(log(-e));
                possign = !possign;
            } else
                prodseq.push_back(e);
        }

        if (sumseq.size() > 0) {
            ex newarg;
            if (options & expand_options::expand_function_args)
                newarg=((possign?_ex1:_ex_1)*mul(prodseq)).expand(options);
            else {
                newarg=(possign?_ex1:_ex_1)*mul(prodseq);
                ex_to<basic>(newarg).setflag(status_flags::purely_indefinite);
            }
            return add(sumseq)+log(newarg);
        } else {
            if (!(options & expand_options::expand_function_args))
                ex_to<basic>(arg).setflag(status_flags::purely_indefinite);
        }
    }

    if (options & expand_options::expand_function_args)
        return log(arg.expand(options)).hold();
    else
        return log(arg).hold();
}

static bool log_info(const ex & x, unsigned inf)
{
    switch (inf) {
    case info_flags::expanded:
        return x.info(inf);
    case info_flags::real:
        return x.info(info_flags::positive);
    case info_flags::positive:
        if(x.info(info_flags::real)){
            if (x>_ex1)
                return true;
            else return false;
        }
        else return false;
    case info_flags::negative:
        if(x.info(info_flags::real)){
            if(x>_ex0 && x<_ex1)
                return true;
            else return false;
        }
        else return false;
    default:
        return false;
    }
}

static ex log_deriv(const ex & x, unsigned deriv_param)
{
    GINAC_ASSERT(deriv_param==0);

    // d/dx log(x) -> 1/x
    return power(x, _ex_1);
}

static ex log_series(const ex &arg,
                     const relational &rel,
                     int order,
                     unsigned options)
{
    GINAC_ASSERT(is_a<symbol>(rel.lhs()));
    ex arg_pt;
    bool must_expand_arg = false;
    // maybe substitution of rel into arg fails because of a pole
    try {
        arg_pt = arg.subs(rel, subs_options::no_pattern);
        if (is_exactly_a<infinity>(arg_pt)) {
            must_expand_arg = true;
        }
    } catch (pole_error) {
        must_expand_arg = true;
    }
    catch (indeterminate_error) {
        must_expand_arg = true;
    }
    // or we are at the branch point anyways
    if (arg_pt.is_zero())
        must_expand_arg = true;

    if (arg.diff(ex_to<symbol>(rel.lhs())).is_zero()) {
        throw do_taylor();
    }

    if (must_expand_arg) {
        // method:
        // This is the branch point: Series expand the argument first, then
        // trivially factorize it to isolate that part which has constant
        // leading coefficient in this fashion:
        //   x^n + x^(n+1) +...+ Order(x^(n+m))  ->  x^n * (1 + x +...+ Order(x^m)).
        // Return a plain n*log(x) for the x^n part and series expand the
        // other part.  Add them together and reexpand again in order to have
        // one unnested pseries object.  All this also works for negative n.
        pseries argser;          // series expansion of log's argument
        unsigned extra_ord = 0;  // extra expansion order
        do {
            // oops, the argument expanded to a pure Order(x^something)...
            argser = ex_to<pseries>(arg.series(rel, order+extra_ord, options));
            ++extra_ord;
        } while (!argser.is_terminating() && argser.nops()==1);

        const symbol &s = ex_to<symbol>(rel.lhs());
        const ex &point = rel.rhs();
        const numeric &num = argser.ldegree(s);
        long n = num.to_long();
        epvector seq;
        // construct what we carelessly called the n*log(x) term above
        const ex coeff = argser.coeff(s, n);
        // expand the log, but only if coeff is real and > 0, since otherwise
        // it would make the branch cut run into the wrong direction
        if (coeff.info(info_flags::positive))
            seq.emplace_back(n*log(s-point)+log(coeff), _ex0);
        else
            seq.emplace_back(log(coeff*pow(s-point, n)), _ex0);

        if (!argser.is_terminating() || argser.nops()!=1) {
            // in this case n more (or less) terms are needed
            // (sadly, to generate them, we have to start from the beginning)
            if (n == 0 and coeff.is_equal(_ex1)) {
                epvector epv;
                ex acc = (new pseries(rel, epv))->setflag(status_flags::dynallocated);
                epv.reserve(2);
                epv.emplace_back(-1, _ex0);
                epv.emplace_back(Order(_ex1), order);
                ex rest = pseries(rel, epv).add_series(argser);
                for (int i = order-1; i>0; --i) {
                    epvector cterm;
                    cterm.reserve(1);
                    cterm.emplace_back((i%2) != 0 ? _ex1/i : _ex_1/i, _ex0);
                    acc = pseries(rel, cterm).add_series(ex_to<pseries>(acc));
                    acc = (ex_to<pseries>(rest)).mul_series(ex_to<pseries>(acc));
                }
                return acc;
            }
            const ex newarg = ex_to<pseries>((arg/coeff).series(rel, order+n, options)).shift_exponents(-n).convert_to_poly(true);
            return pseries(rel, seq).add_series(ex_to<pseries>(log(newarg).series(rel, order, options)));
        }  // it was a monomial
        return pseries(rel, seq);
    }
    if (((options & series_options::suppress_branchcut) == 0u) &&
        arg_pt.info(info_flags::negative)) {
        // method:
        // This is the branch cut: assemble the primitive series manually and
        // then add the corresponding complex step function.
        const symbol &s = ex_to<symbol>(rel.lhs());
        const ex &point = rel.rhs();
        const symbol foo;
        const ex replarg = series(log(arg), s==foo, order).subs(foo==point, subs_options::no_pattern);
        epvector seq;
        seq.emplace_back(-I*csgn(arg*I)*Pi, _ex0);
        seq.emplace_back(Order(_ex1), order);
        return series(replarg - I*Pi + pseries(rel, seq), rel, order);
    }
    throw do_taylor();  // caught by function::series()
}

static ex log_real_part(const ex & x)
{
    if (x.info(info_flags::positive))
        return log(x).hold();
    return log(abs(x));
}

static ex log_imag_part(const ex & x)
{
    if (x.info(info_flags::positive))
        return _ex0;
    return atan2(ginacsym::imag_part(x), ginacsym::real_part(x));
}

static ex log_conjugate(const ex & x)
{
    // conjugate(log(x))==log(conjugate(x)) unless on the branch cut which
    // runs along the negative real axis.
    if (x.info(info_flags::positive)) {
        return log(x);
    }
    if (is_exactly_a<numeric>(x) &&
        !x.imag_part().is_zero()) {
        return log(x.conjugate());
    }
    return conjugate_function(log(x)).hold();
}

REGISTER_FUNCTION(log, evalf_func(log_evalf).
                       eval_func(log_eval).
                       expand_func(log_expand).
                       info_func(log_info).
                       derivative_func(log_deriv).
                       series_func(log_series).
                       real_part_func(log_real_part).
                       imag_part_func(log_imag_part).
                       conjugate_func(log_conjugate).
                       latex_name("\\ln"));

//////////
// General logarithm
// This only has shortcuts and delegates everything else to log(arg)
//////////

static ex logb_evalf(const ex & x, const ex & base)
{
    if ((base - exp(_ex1).hold()).is_zero()) {
        if (is_exactly_a<numeric>(x))
            return log(ex_to<numeric>(x));
        return log(x);
    }
    if (is_exactly_a<numeric>(x) and is_exactly_a<numeric>(base))
        return log(ex_to<numeric>(x),ex_to<numeric>(base));

    return mul(log(x), pow(log(base), _ex_1));
}

static ex logb_eval(const ex & x, const ex & base)
{
    if (is_exactly_a<numeric>(x) and !x.info(info_flags::crational)
        and is_exactly_a<numeric>(base) and !base.info(info_flags::crational)) {
//        const numeric& a = ex_to<numeric>(x);
//        const numeric& b = ex_to<numeric>(base);
//        if (b.info(info_flags::real) and a.info(info_flags::real)) {
//            bool israt;
//            numeric ret = a.ratlog(b, israt);
//            if (israt)
//                return ret;
//        }
        return log(ex_to<numeric>(x),ex_to<numeric>(base));
    }

    if ((base - exp(_ex1).hold()).is_zero())
        return log_eval(x);

    // log(base^t, base) -> t
    if (is_exactly_a<power>(x)) {
        if (x.op(0).is_equal(base) and x.op(1).info(info_flags::real))
            return x.op(1);
    }

    // log(float) -> float
    if (is_a<numeric>(x) && !x.info(info_flags::crational))
        return log(ex_to<numeric>(x));

    // log(oo) -> oo
    if (is_a<infinity>(x)) {
        return Infinity;
    }

    // log(x)/log(base)
    return mul(log(x), pow(log(base), _ex_1));
}

static bool logb_info(const ex & y, const ex & x, unsigned inf)
{
    switch (inf) {
    case info_flags::expanded:
    case info_flags::real:
        return y.info(inf) && x.info(inf);
    case info_flags::positive:
    case info_flags::negative:
    case info_flags::nonnegative:
        return y.info(info_flags::real) && x.info(info_flags::real)
               && y.info(inf);
    default:
        return false;
    }
}

REGISTER_FUNCTION(logb, eval_func(logb_eval).
                        evalf_func(logb_evalf).
                        info_func(logb_info).
                        latex_name("\\log"));


} // namespace ginacsym
