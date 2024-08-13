/** @file inifcns.cpp
 *
 *  Implementation of ginacsym's initially known functions. */

/*
 *  ginacsym Copyright (C) 1999-2023 Johannes Gutenberg University Mainz, Germany
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
#include "lst.h"
#include "fderivative.h"
#include "matrix.h"
#include "mul.h"
#include "power.h"
#include "operators.h"
#include "relational.h"
#include "pseries.h"
#include "symbol.h"
#include "symmetry.h"
#include "utils.h"
#include "add.h"

#include "utility.h"
#include "infinity.h"
#include "ginacwrapper.h"

#include "flint/acb.h"
#include "flint/acb_hypgeom.h"

#include "flint/fmpz_poly.h"
#include "flint/fmpq.h"
#include "flint/acb.h"
#include "flint/acb_hypgeom.h"

#include <stdexcept>
#include <vector>

namespace ginacsym {

//////////
// complex conjugate
//////////

static ex conjugate_evalf(const ex & arg)
{
	if (is_exactly_a<numeric>(arg)) {
		return ex_to<numeric>(arg).conjugate();
	}
	return conjugate_function(arg).hold();
}

static ex conjugate_eval(const ex & arg)
{
	return arg.conjugate();
}

static void conjugate_print_latex(const ex & arg, const print_context & c)
{
	c.s << "\\bar{"; arg.print(c); c.s << "}";
}

static ex conjugate_conjugate(const ex & arg)
{
	return arg;
}

// If x is real then U.diff(x)-I*V.diff(x) represents both conjugate(U+I*V).diff(x) 
// and conjugate((U+I*V).diff(x))
static ex conjugate_expl_derivative(const ex & arg, const symbol & s)
{
	if (s.info(info_flags::real))
		return conjugate(arg.diff(s));
	else {
		exvector vec_arg;
		vec_arg.push_back(arg);
		return fderivative(ex_to<function>(conjugate(arg)).get_serial(),0,vec_arg).hold()*arg.diff(s);
	}
}

static ex conjugate_real_part(const ex & arg)
{
	return arg.real_part();
}

static ex conjugate_imag_part(const ex & arg)
{
	return -arg.imag_part();
}

static bool func_arg_info(const ex & arg, unsigned inf)
{
	// for some functions we can return the info() of its argument
	// (think of conjugate())
	switch (inf) {
		case info_flags::polynomial:
		case info_flags::integer_polynomial:
		case info_flags::cinteger_polynomial:
		case info_flags::rational_polynomial:
		case info_flags::real:
		case info_flags::rational:
		case info_flags::integer:
		case info_flags::crational:
		case info_flags::cinteger:
		case info_flags::even:
		case info_flags::odd:
		case info_flags::prime:
		case info_flags::crational_polynomial:
		case info_flags::rational_function:
		case info_flags::positive:
		case info_flags::negative:
		case info_flags::nonnegative:
		case info_flags::posint:
		case info_flags::negint:
		case info_flags::nonnegint:
		case info_flags::has_indices:
			return arg.info(inf);
	}
	return false;
}

static bool conjugate_info(const ex & arg, unsigned inf)
{
	return func_arg_info(arg, inf);
}

REGISTER_FUNCTION(conjugate_function, eval_func(conjugate_eval).
                                      evalf_func(conjugate_evalf).
                                      expl_derivative_func(conjugate_expl_derivative).
                                      info_func(conjugate_info).
                                      print_func<print_latex>(conjugate_print_latex).
                                      conjugate_func(conjugate_conjugate).
                                      real_part_func(conjugate_real_part).
                                      imag_part_func(conjugate_imag_part).
                                      set_name("conjugate","conjugate"));

//////////
// real part
//////////

static ex real_part_evalf(const ex & arg)
{
	if (is_exactly_a<numeric>(arg)) {
		return ex_to<numeric>(arg).real();
	}
	return real_part_function(arg).hold();
}

static ex real_part_eval(const ex & arg)
{
	return arg.real_part();
}

static void real_part_print_latex(const ex & arg, const print_context & c)
{
    c.s << "\\Re\\left("; arg.print(c); c.s << "\\right)";
}

static ex real_part_conjugate(const ex & arg)
{
	return real_part_function(arg).hold();
}

static ex real_part_real_part(const ex & arg)
{
	return real_part_function(arg).hold();
}

static ex real_part_imag_part(const ex & arg)
{
	return 0;
}

// If x is real then Re(e).diff(x) is equal to Re(e.diff(x)) 
static ex real_part_expl_derivative(const ex & arg, const symbol & s)
{
	if (s.info(info_flags::real))
		return real_part_function(arg.diff(s));
	else {
		exvector vec_arg;
		vec_arg.push_back(arg);
		return fderivative(ex_to<function>(real_part(arg)).get_serial(),0,vec_arg).hold()*arg.diff(s);
	}
}

REGISTER_FUNCTION(real_part_function, eval_func(real_part_eval).
                                      evalf_func(real_part_evalf).
                                      expl_derivative_func(real_part_expl_derivative).
                                      print_func<print_latex>(real_part_print_latex).
                                      conjugate_func(real_part_conjugate).
                                      real_part_func(real_part_real_part).
                                      imag_part_func(real_part_imag_part).
                                      set_name("real_part","real_part"));

//////////
// imag part
//////////

static ex imag_part_evalf(const ex & arg)
{
	if (is_exactly_a<numeric>(arg)) {
		return ex_to<numeric>(arg).imag();
	}
	return imag_part_function(arg).hold();
}

static ex imag_part_eval(const ex & arg)
{
	return arg.imag_part();
}

static void imag_part_print_latex(const ex & arg, const print_context & c)
{
    c.s << "\\Im\\left("; arg.print(c); c.s << "\\right)";
}

static ex imag_part_conjugate(const ex & arg)
{
	return imag_part_function(arg).hold();
}

static ex imag_part_real_part(const ex & arg)
{
	return imag_part_function(arg).hold();
}

static ex imag_part_imag_part(const ex & arg)
{
	return 0;
}

// If x is real then Im(e).diff(x) is equal to Im(e.diff(x)) 
static ex imag_part_expl_derivative(const ex & arg, const symbol & s)
{
	if (s.info(info_flags::real))
		return imag_part_function(arg.diff(s));
	else {
		exvector vec_arg;
		vec_arg.push_back(arg);
		return fderivative(ex_to<function>(imag_part(arg)).get_serial(),0,vec_arg).hold()*arg.diff(s);
	}
}

REGISTER_FUNCTION(imag_part_function, eval_func(imag_part_eval).
                                      evalf_func(imag_part_evalf).
                                      expl_derivative_func(imag_part_expl_derivative).
                                      print_func<print_latex>(imag_part_print_latex).
                                      conjugate_func(imag_part_conjugate).
                                      real_part_func(imag_part_real_part).
                                      imag_part_func(imag_part_imag_part).
                                      set_name("imag_part","imag_part"));

//////////
// absolute value
//////////

static ex abs_evalf(const ex & arg)
{
	if (is_exactly_a<numeric>(arg))
		return abs(ex_to<numeric>(arg));
	
	return abs(arg).hold();
}

static ex abs_eval(const ex & arg)
{
	if (is_exactly_a<numeric>(arg))
		return abs(ex_to<numeric>(arg));

	if (arg.info(info_flags::nonnegative))
		return arg;

	if (arg.info(info_flags::negative) || (-arg).info(info_flags::nonnegative))
		return -arg;

	if (is_ex_the_function(arg, abs))
		return arg;

	if (is_ex_the_function(arg, exp))
		return exp(arg.op(0).real_part());

	if (is_exactly_a<power>(arg)) {
		const ex& base = arg.op(0);
		const ex& exponent = arg.op(1);
		if (base.info(info_flags::positive) || exponent.info(info_flags::real))
			return pow(abs(base), exponent.real_part());
	}

	if (is_ex_the_function(arg, conjugate_function))
		return abs(arg.op(0));

	if (is_ex_the_function(arg, step))
		return arg;

	return abs(arg).hold();
}

static ex abs_expand(const ex & arg, unsigned options)
{
	if ((options & expand_options::expand_transcendental)
		&& is_exactly_a<mul>(arg)) {
		exvector prodseq;
		prodseq.reserve(arg.nops());
		for (const_iterator i = arg.begin(); i != arg.end(); ++i) {
			if (options & expand_options::expand_function_args)
				prodseq.push_back(abs(i->expand(options)));
			else
				prodseq.push_back(abs(*i));
		}
		return dynallocate<mul>(prodseq).setflag(status_flags::expanded);
	}

	if (options & expand_options::expand_function_args)
		return abs(arg.expand(options)).hold();
	else
		return abs(arg).hold();
}

static ex abs_expl_derivative(const ex & arg, const symbol & s)
{
	ex diff_arg = arg.diff(s);
	return (diff_arg*arg.conjugate()+arg*diff_arg.conjugate())/2/abs(arg);
}

static void abs_print_latex(const ex & arg, const print_context & c)
{
	c.s << "{|"; arg.print(c); c.s << "|}";
}

static void abs_print_csrc_float(const ex & arg, const print_context & c)
{
	c.s << "fabs("; arg.print(c); c.s << ")";
}

static ex abs_conjugate(const ex & arg)
{
	return abs(arg).hold();
}

static ex abs_real_part(const ex & arg)
{
	return abs(arg).hold();
}

static ex abs_imag_part(const ex& arg)
{
	return 0;
}

static ex abs_power(const ex & arg, const ex & exp)
{
	if ((is_a<numeric>(exp) && ex_to<numeric>(exp).is_even()) || exp.info(info_flags::even)) {
		if (arg.info(info_flags::real) || arg.is_equal(arg.conjugate()))
			return pow(arg, exp);
		else
			return pow(arg, exp/2) * pow(arg.conjugate(), exp/2);
	} else
		return power(abs(arg), exp).hold();
}

bool abs_info(const ex & arg, unsigned inf)
{
	switch (inf) {
		case info_flags::integer:
		case info_flags::even:
		case info_flags::odd:
		case info_flags::prime:
			return arg.info(inf);
		case info_flags::nonnegint:
			return arg.info(info_flags::integer);
		case info_flags::nonnegative:
		case info_flags::real:
			return true;
		case info_flags::negative:
			return false;
		case info_flags::positive:
			return arg.info(info_flags::positive) || arg.info(info_flags::negative);
		case info_flags::has_indices: {
			if (arg.info(info_flags::has_indices))
				return true;
			else
				return false;
		}
	}
	return false;
}

REGISTER_FUNCTION(abs, eval_func(abs_eval).
                       evalf_func(abs_evalf).
                       expand_func(abs_expand).
                       expl_derivative_func(abs_expl_derivative).
                       info_func(abs_info).
                       print_func<print_latex>(abs_print_latex).
                       print_func<print_csrc_float>(abs_print_csrc_float).
                       print_func<print_csrc_double>(abs_print_csrc_float).
                       conjugate_func(abs_conjugate).
                       real_part_func(abs_real_part).
                       imag_part_func(abs_imag_part).
                       power_func(abs_power));

//////////
// Step function
//////////

static ex step_evalf(const ex & arg)
{
	if (is_exactly_a<numeric>(arg))
		return step(ex_to<numeric>(arg));
	
	return step(arg).hold();
}

static ex step_eval(const ex & arg)
{
	if (is_exactly_a<numeric>(arg))
		return step(ex_to<numeric>(arg));
	
	else if (is_exactly_a<mul>(arg) &&
	         is_exactly_a<numeric>(arg.op(arg.nops()-1))) {
		numeric oc = ex_to<numeric>(arg.op(arg.nops()-1));
		if (oc.is_real()) {
			if (oc > 0)
				// step(42*x) -> step(x)
				return step(arg/oc).hold();
			else
				// step(-42*x) -> step(-x)
				return step(-arg/oc).hold();
		}
		if (oc.real().is_zero()) {
			if (oc.imag() > 0)
				// step(42*I*x) -> step(I*x)
				return step(I*arg/oc).hold();
			else
				// step(-42*I*x) -> step(-I*x)
				return step(-I*arg/oc).hold();
		}
	}
	
	return step(arg).hold();
}

static ex step_series(const ex & arg,
                      const relational & rel,
                      int order,
                      unsigned options)
{
	const ex arg_pt = arg.subs(rel, subs_options::no_pattern);
	if (arg_pt.info(info_flags::numeric)
	    && ex_to<numeric>(arg_pt).real().is_zero()
	    && !(options & series_options::suppress_branchcut))
		throw (std::domain_error("step_series(): on imaginary axis"));
	
	epvector seq { expair(step(arg_pt), _ex0) };
	return pseries(rel, std::move(seq));
}

static ex step_conjugate(const ex& arg)
{
	return step(arg).hold();
}

static ex step_real_part(const ex& arg)
{
	return step(arg).hold();
}

static ex step_imag_part(const ex& arg)
{
	return 0;
}

REGISTER_FUNCTION(step, eval_func(step_eval).
                        evalf_func(step_evalf).
                        series_func(step_series).
                        conjugate_func(step_conjugate).
                        real_part_func(step_real_part).
                        imag_part_func(step_imag_part));


//////////
// Heaviside function
//////////

static ex heaviside_evalf(const ex & arg)
{
    if (is_exactly_a<numeric>(arg)
        and arg.info(info_flags::real)
        and not arg.is_zero())
        return step(ex_to<numeric>(arg));

    return heaviside(arg).hold();
}

static ex heaviside_eval(const ex & arg)
{
    if (arg.info(info_flags::positive))
        return _ex1;
    if (arg.info(info_flags::negative))
        return _ex0;
    if (is_exactly_a<numeric>(arg))
        return heaviside_evalf(arg);

    if (is_exactly_a<mul>(arg)) {
        const numeric& oc = ex_to<mul>(arg).get_overall_coeff();
        if (oc.is_real()) {
            if (oc > 0)
                // step(42*x) -> step(x)
                return heaviside(arg/oc).hold();

            // step(-42*x) -> step(-x)
            return heaviside(-arg/oc).hold();
        }
        if (oc.real().is_zero()) {
            if (oc.imag() > 0)
                // step(42*I*x) -> step(I*x)
                return heaviside(I*arg/oc).hold();

            // step(-42*I*x) -> step(-I*x)
            return heaviside(-I*arg/oc).hold();
        }
    }

    return heaviside(arg).hold();
}

static ex heaviside_series(const ex & arg,
                           const relational & rel,
                           int order,
                           unsigned options)
{
    const ex arg_pt = arg.subs(rel, subs_options::no_pattern);
    if (is_exactly_a<numeric>(arg_pt)
        && ex_to<numeric>(arg_pt).real().is_zero()
        && ((options & series_options::suppress_branchcut) == 0u))
        throw (std::domain_error("heaviside_series(): on imaginary axis"));

    epvector seq;
    seq.emplace_back(heaviside(arg_pt), _ex0);
    return pseries(rel,seq);
}

static ex heaviside_conjugate(const ex& arg)
{
    return heaviside(arg).hold();
}

static ex heaviside_real_part(const ex& arg)
{
    return heaviside(arg).hold();
}

static ex heaviside_imag_part(const ex& arg)
{
    return 0;
}

REGISTER_FUNCTION(heaviside, eval_func(heaviside_eval).
                             evalf_func(heaviside_evalf).
                             series_func(heaviside_series).
                             conjugate_func(heaviside_conjugate).
                             real_part_func(heaviside_real_part).
                             imag_part_func(heaviside_imag_part));


static ex cases_eval(const ex & arg)
{
    if (not is_exactly_a<exprseq>(arg))
        throw std::runtime_error("cases argument not a sequence");
    bool default_seen = false;
    ex deflt;
    for (auto case_ : arg) {
        if (not is_exactly_a<exprseq>(case_)) {
            if (not default_seen) {
                deflt = case_;
                default_seen = true;
            }
            continue;
        }
        const exprseq& seq = ex_to<exprseq>(case_);
        if (seq.nops() == 1) {
            if (not default_seen) {
                deflt = seq[0];
                default_seen = true;
            }
            continue;
        }
        if (seq.nops() != 2)
            throw std::runtime_error("cases case not a pair");
        const ex& cond = seq[0];
        if (is_exactly_a<numeric>(cond)) {
            if (not cond.is_zero()
                and not default_seen) {
                deflt = seq[1];
                default_seen = true;
            }
            continue;
        }
        if (is_exactly_a<relational>(cond)) {
            auto res = ex_to<relational>(cond).decide();
            if (res == relational::result::True)
                return seq[1];
            if (res == relational::result::False)
                continue;
            // undecidable relation
            return cases(arg).hold();
        }
        throw std::runtime_error("cases with meaningless condition");
    }
    if (default_seen)
        return deflt;
    return cases(arg).hold();
}

static ex cases_evalf(const ex & arg)
{
    return cases(arg).hold();
}

static ex cases_conjugate(const ex & arg)
{
    return cases(arg).hold();
}

static ex cases_real_part(const ex & arg)
{
    return cases(arg).hold();
}

static ex cases_imag_part(const ex & arg)
{
    return cases(arg).hold();
}

static ex cases_subs(const exmap& m, const ex & arg) {
    bool default_seen = false;
    ex deflt;
    for (auto case_ : arg) {
        if (not is_exactly_a<exprseq>(case_)) {
            if (not default_seen) {
                deflt = case_;
                default_seen = true;
            }
            continue;
        }
        const exprseq& seq = ex_to<exprseq>(case_);
        if (seq.nops() == 1) {
            if (not default_seen) {
                deflt = seq[0];
                default_seen = true;
            }
            continue;
        }
        if (seq.nops() != 2)
            throw std::runtime_error("cases case not a pair");
        const ex& cond = seq[0].subs(m);
        if (is_exactly_a<numeric>(cond)) {
            if (not cond.is_zero()
                and not default_seen) {
                deflt = seq[1];
                default_seen = true;
            }
            continue;
        }
        if (is_exactly_a<relational>(cond)) {
            auto res = ex_to<relational>(cond).decide();
            if (res == relational::result::True)
                return seq[1].subs(m);
            if (res == relational::result::False)
                continue;
            // undecidable relation
            return cases(arg).hold();
        }
        throw std::runtime_error("cases with meaningless condition");
    }
    if (default_seen)
        return deflt.subs(m);
    return cases(arg).hold();
}

REGISTER_FUNCTION(cases, eval_func(cases_eval).
                         evalf_func(cases_evalf).
                         conjugate_func(cases_conjugate).
                         real_part_func(cases_real_part).
                         imag_part_func(cases_imag_part).
                         subs_func(cases_subs));

//////////
// Complex sign
//////////

static ex csgn_evalf(const ex & arg)
{
	if (is_exactly_a<numeric>(arg))
		return csgn(ex_to<numeric>(arg));
	
	return csgn(arg).hold();
}

static ex csgn_eval(const ex & arg)
{
	if (is_exactly_a<numeric>(arg))
		return csgn(ex_to<numeric>(arg));
	
	else if (is_exactly_a<mul>(arg) &&
	         is_exactly_a<numeric>(arg.op(arg.nops()-1))) {
		numeric oc = ex_to<numeric>(arg.op(arg.nops()-1));
		if (oc.is_real()) {
			if (oc > 0)
				// csgn(42*x) -> csgn(x)
				return csgn(arg/oc).hold();
			else
				// csgn(-42*x) -> -csgn(x)
				return -csgn(arg/oc).hold();
		}
		if (oc.real().is_zero()) {
			if (oc.imag() > 0)
				// csgn(42*I*x) -> csgn(I*x)
				return csgn(I*arg/oc).hold();
			else
				// csgn(-42*I*x) -> -csgn(I*x)
				return -csgn(I*arg/oc).hold();
		}
	}
	
	return csgn(arg).hold();
}

static ex csgn_series(const ex & arg,
                      const relational & rel,
                      int order,
                      unsigned options)
{
	const ex arg_pt = arg.subs(rel, subs_options::no_pattern);
	if (arg_pt.info(info_flags::numeric)
	    && ex_to<numeric>(arg_pt).real().is_zero()
	    && !(options & series_options::suppress_branchcut))
		throw (std::domain_error("csgn_series(): on imaginary axis"));
	
	epvector seq { expair(csgn(arg_pt), _ex0) };
	return pseries(rel, std::move(seq));
}

static ex csgn_conjugate(const ex& arg)
{
	return csgn(arg).hold();
}

static ex csgn_real_part(const ex& arg)
{
	return csgn(arg).hold();
}

static ex csgn_imag_part(const ex& arg)
{
	return 0;
}

static ex csgn_power(const ex & arg, const ex & exp)
{
	if (is_a<numeric>(exp) && exp.info(info_flags::positive) && ex_to<numeric>(exp).is_integer()) {
		if (ex_to<numeric>(exp).is_odd())
			return csgn(arg).hold();
		else
			return power(csgn(arg), _ex2).hold();
	} else
		return power(csgn(arg), exp).hold();
}


REGISTER_FUNCTION(csgn, eval_func(csgn_eval).
                        evalf_func(csgn_evalf).
                        series_func(csgn_series).
                        conjugate_func(csgn_conjugate).
                        real_part_func(csgn_real_part).
                        imag_part_func(csgn_imag_part).
                        power_func(csgn_power));


//////////
// Eta function: eta(x,y) == log(x*y) - log(x) - log(y).
// This function is closely related to the unwinding number K, sometimes found
// in modern literature: K(z) == (z-log(exp(z)))/(2*Pi*I).
//////////

static ex eta_evalf(const ex &x, const ex &y)
{
	// It seems like we basically have to replicate the eval function here,
	// since the expression might not be fully evaluated yet.
	if (x.info(info_flags::positive) || y.info(info_flags::positive))
		return _ex0;

	if (x.info(info_flags::numeric) &&	y.info(info_flags::numeric)) {
		const numeric nx = ex_to<numeric>(x);
		const numeric ny = ex_to<numeric>(y);
		const numeric nxy = ex_to<numeric>(x*y);
		int cut = 0;
		if (nx.is_real() && nx.is_negative())
			cut -= 4;
		if (ny.is_real() && ny.is_negative())
			cut -= 4;
		if (nxy.is_real() && nxy.is_negative())
			cut += 4;
		return evalf(I/4*Pi)*((csgn(-imag(nx))+1)*(csgn(-imag(ny))+1)*(csgn(imag(nxy))+1)-
		                      (csgn(imag(nx))+1)*(csgn(imag(ny))+1)*(csgn(-imag(nxy))+1)+cut);
	}

	return eta(x,y).hold();
}

static ex eta_eval(const ex &x, const ex &y)
{
	// trivial:  eta(x,c) -> 0  if c is real and positive
	if (x.info(info_flags::positive) || y.info(info_flags::positive))
		return _ex0;

	if (x.info(info_flags::numeric) &&	y.info(info_flags::numeric)) {
		// don't call eta_evalf here because it would call Pi.evalf()!
		const numeric nx = ex_to<numeric>(x);
		const numeric ny = ex_to<numeric>(y);
		const numeric nxy = ex_to<numeric>(x*y);
		int cut = 0;
		if (nx.is_real() && nx.is_negative())
			cut -= 4;
		if (ny.is_real() && ny.is_negative())
			cut -= 4;
		if (nxy.is_real() && nxy.is_negative())
			cut += 4;
		return (I/4)*Pi*((csgn(-imag(nx))+1)*(csgn(-imag(ny))+1)*(csgn(imag(nxy))+1)-
		                 (csgn(imag(nx))+1)*(csgn(imag(ny))+1)*(csgn(-imag(nxy))+1)+cut);
	}
	
	return eta(x,y).hold();
}

static ex eta_series(const ex & x, const ex & y,
                     const relational & rel,
                     int order,
                     unsigned options)
{
	const ex x_pt = x.subs(rel, subs_options::no_pattern);
	const ex y_pt = y.subs(rel, subs_options::no_pattern);
	if ((x_pt.info(info_flags::numeric) && x_pt.info(info_flags::negative)) ||
	    (y_pt.info(info_flags::numeric) && y_pt.info(info_flags::negative)) ||
	    ((x_pt*y_pt).info(info_flags::numeric) && (x_pt*y_pt).info(info_flags::negative)))
			throw (std::domain_error("eta_series(): on discontinuity"));
	epvector seq { expair(eta(x_pt,y_pt), _ex0) };
	return pseries(rel, std::move(seq));
}

static ex eta_conjugate(const ex & x, const ex & y)
{
	return -eta(x, y).hold();
}

static ex eta_real_part(const ex & x, const ex & y)
{
	return 0;
}

static ex eta_imag_part(const ex & x, const ex & y)
{
	return -I*eta(x, y).hold();
}

REGISTER_FUNCTION(eta, eval_func(eta_eval).
                       evalf_func(eta_evalf).
                       series_func(eta_series).
                       latex_name("\\eta").
                       set_symmetry(sy_symm(0, 1)).
                       conjugate_func(eta_conjugate).
                       real_part_func(eta_real_part).
                       imag_part_func(eta_imag_part));


//////////
// dilogarithm
//////////

static ex Li2_evalf(const ex & x)
{
    if (is_exactly_a<numeric>(x))
        return Li2(ex_to<numeric>(x));

    return Li2(x).hold();
}

static ex Li2_eval(const ex & x)
{
    if (x.info(info_flags::numeric)) {
        // Li2(0) -> 0
        if (x.is_zero())
            return _ex0;
        // Li2(1) -> Pi^2/6
        if (x.is_equal(_ex1))
            return power(Pi,_ex2)/_ex6;
        // Li2(1/2) -> Pi^2/12 - log(2)^2/2
        if (x.is_equal(_ex1_2))
            return power(Pi,_ex2)/_ex12 + power(log(_ex2),_ex2)*_ex_1_2;
        // Li2(-1) -> -Pi^2/12
        if (x.is_equal(_ex_1))
            return -power(Pi,_ex2)/_ex12;
        // Li2(I) -> -Pi^2/48+Catalan*I
        if (x.is_equal(I))
            return power(Pi,_ex2)/_ex_48 + Catalan*I;
        // Li2(-I) -> -Pi^2/48-Catalan*I
        if (x.is_equal(-I))
            return power(Pi,_ex2)/_ex_48 - Catalan*I;
        // Li2(float)
        if (!x.info(info_flags::crational))
            return Li2(ex_to<numeric>(x));
    }

    return Li2(x).hold();
}

static ex Li2_deriv(const ex & x, unsigned deriv_param)
{
    GINAC_ASSERT(deriv_param==0);

    // d/dx Li2(x) -> -log(1-x)/x
    return -log(_ex1-x)/x;
}

static ex Li2_series(const ex &x, const relational &rel, int order, unsigned options)
{
    const ex x_pt = x.subs(rel, subs_options::no_pattern);
    if (x_pt.info(info_flags::numeric)) {
        // First special case: x==0 (derivatives have poles)
        if (x_pt.is_zero()) {
            // method:
            // The problem is that in d/dx Li2(x==0) == -log(1-x)/x we cannot
            // simply substitute x==0.  The limit, however, exists: it is 1.
            // We also know all higher derivatives' limits:
            // (d/dx)^n Li2(x) == n!/n^2.
            // So the primitive series expansion is
            // Li2(x==0) == x + x^2/4 + x^3/9 + ...
            // and so on.
            // We first construct such a primitive series expansion manually in
            // a dummy symbol s and then insert the argument's series expansion
            // for s.  Reexpanding the resulting series returns the desired
            // result.
            const symbol s;
            ex ser;
            // manually construct the primitive expansion
            for (int i=1; i<order; ++i)
                ser += pow(s,i) / pow(numeric(i), *_num2_p);
            // substitute the argument's series expansion
            ser = ser.subs(s==x.series(rel, order), subs_options::no_pattern);
            // maybe that was terminating, so add a proper order term
            epvector nseq { expair(Order(_ex1), order) };
            ser += pseries(rel, std::move(nseq));
            // reexpanding it will collapse the series again
            return ser.series(rel, order);
            // NB: Of course, this still does not allow us to compute anything
            // like sin(Li2(x)).series(x==0,2), since then this code here is
            // not reached and the derivative of sin(Li2(x)) doesn't allow the
            // substitution x==0.  Probably limits *are* needed for the general
            // cases.  In case L'Hospital's rule is implemented for limits and
            // basic::series() takes care of this, this whole block is probably
            // obsolete!
        }
        // second special case: x==1 (branch point)
        if (x_pt.is_equal(_ex1)) {
            // method:
            // construct series manually in a dummy symbol s
            const symbol s;
            ex ser = zeta(_ex2);
            // manually construct the primitive expansion
            for (int i=1; i<order; ++i)
                ser += pow(1-s,i) * (numeric(1,i)*(I*Pi+log(s-1)) - numeric(1,i*i));
            // substitute the argument's series expansion
            ser = ser.subs(s==x.series(rel, order), subs_options::no_pattern);
            // maybe that was terminating, so add a proper order term
            epvector nseq { expair(Order(_ex1), order) };
            ser += pseries(rel, std::move(nseq));
            // reexpanding it will collapse the series again
            return ser.series(rel, order);
        }
        // third special case: x real, >=1 (branch cut)
        if (!(options & series_options::suppress_branchcut) &&
            ex_to<numeric>(x_pt).is_real() && ex_to<numeric>(x_pt)>1) {
            // method:
            // This is the branch cut: assemble the primitive series manually
            // and then add the corresponding complex step function.
            const symbol &s = ex_to<symbol>(rel.lhs());
            const ex point = rel.rhs();
            const symbol foo;
            epvector seq;
            // zeroth order term:
            seq.push_back(expair(Li2(x_pt), _ex0));
            // compute the intermediate terms:
            ex replarg = series(Li2(x), s==foo, order);
            for (size_t i=1; i<replarg.nops()-1; ++i)
                seq.push_back(expair((replarg.op(i)/power(s-foo,i)).series(foo==point,1,options).op(0).subs(foo==s, subs_options::no_pattern),i));
            // append an order term:
            seq.push_back(expair(Order(_ex1), replarg.nops()-1));
            return pseries(rel, std::move(seq));
        }
    }
    // all other cases should be safe, by now:
    throw do_taylor();  // caught by function::series()
}

static ex Li2_conjugate(const ex & x)
{
    // conjugate(Li2(x))==Li2(conjugate(x)) unless on the branch cuts which
    // run along the positive real axis beginning at 1.
    if (x.info(info_flags::negative)) {
        return Li2(x).hold();
    }
    if (is_exactly_a<numeric>(x) &&
        (!x.imag_part().is_zero() || x < *_num1_p)) {
        return Li2(x.conjugate());
    }
    return conjugate_function(Li2(x)).hold();
}

REGISTER_FUNCTION(Li2, eval_func(Li2_eval).
                       evalf_func(Li2_evalf).
                       derivative_func(Li2_deriv).
                       series_func(Li2_series).
                       conjugate_func(Li2_conjugate).
                       latex_name("\\mathrm{Li}_2"));

//////////
// trilogarithm
//////////

static ex Li3_eval(const ex & x)
{
	if (x.is_zero())
		return x;
	return Li3(x).hold();
}

REGISTER_FUNCTION(Li3, eval_func(Li3_eval).
                       latex_name("\\mathrm{Li}_3"));

//////////
// Derivatives of Riemann's Zeta-function  zetaderiv(0,x)==zeta(x)
//////////

static ex zetaderiv_eval(const ex & n, const ex & x)
{
	if (n.info(info_flags::numeric)) {
		// zetaderiv(0,x) -> zeta(x)
		if (n.is_zero())
			return zeta(x).hold();
	}
	
	return zetaderiv(n, x).hold();
}

static ex zetaderiv_deriv(const ex & n, const ex & x, unsigned deriv_param)
{
	GINAC_ASSERT(deriv_param<2);
	
	if (deriv_param==0) {
		// d/dn zeta(n,x)
		throw(std::logic_error("cannot diff zetaderiv(n,x) with respect to n"));
	}
	// d/dx psi(n,x)
	return zetaderiv(n+1,x);
}

REGISTER_FUNCTION(zetaderiv, eval_func(zetaderiv_eval).
	                       	 derivative_func(zetaderiv_deriv).
  	                         latex_name("\\zeta^\\prime"));

//////////
// factorial
//////////

static ex factorial_evalf(const ex & x)
{
	return factorial(x).hold();
}

static ex factorial_eval(const ex & x)
{
	if (is_exactly_a<numeric>(x))
		return factorial(ex_to<numeric>(x));
	else
		return factorial(x).hold();
}

static void factorial_print_dflt_latex(const ex & x, const print_context & c)
{
	if (is_exactly_a<symbol>(x) ||
	    is_exactly_a<constant>(x) ||
		is_exactly_a<function>(x)) {
		x.print(c); c.s << "!";
	} else {
		c.s << "("; x.print(c); c.s << ")!";
	}
}

static ex factorial_conjugate(const ex & x)
{
	return factorial(x).hold();
}

static ex factorial_real_part(const ex & x)
{
	return factorial(x).hold();
}

static ex factorial_imag_part(const ex & x)
{
	return 0;
}

REGISTER_FUNCTION(factorial, eval_func(factorial_eval).
                             evalf_func(factorial_evalf).
                             print_func<print_dflt>(factorial_print_dflt_latex).
                             print_func<print_latex>(factorial_print_dflt_latex).
                             conjugate_func(factorial_conjugate).
                             real_part_func(factorial_real_part).
                             imag_part_func(factorial_imag_part));

//////////
// binomial
//////////

static ex binomial_evalf(const ex & x, const ex & y)
{
	return binomial(x, y).hold();
}

static ex binomial_sym(const ex & x, const numeric & y)
{
	if (y.is_integer()) {
		if (y.is_nonneg_integer()) {
			const unsigned N = y.to_int();
			if (N == 0) return _ex1;
			if (N == 1) return x;
			ex t = x.expand();
			for (unsigned i = 2; i <= N; ++i)
				t = (t * (x + i - y - 1)).expand() / i;
			return t;
		} else
			return _ex0;
	}

	return binomial(x, y).hold();
}

static ex binomial_eval(const ex & x, const ex &y)
{
	if (is_exactly_a<numeric>(y)) {
		if (is_exactly_a<numeric>(x) && ex_to<numeric>(x).is_integer())
			return binomial(ex_to<numeric>(x), ex_to<numeric>(y));
		else
			return binomial_sym(x, ex_to<numeric>(y));
	} else
		return binomial(x, y).hold();
}

// At the moment the numeric evaluation of a binomial function always
// gives a real number, but if this would be implemented using the gamma
// function, also complex conjugation should be changed (or rather, deleted).
static ex binomial_conjugate(const ex & x, const ex & y)
{
	return binomial(x,y).hold();
}

static ex binomial_real_part(const ex & x, const ex & y)
{
	return binomial(x,y).hold();
}

static ex binomial_imag_part(const ex & x, const ex & y)
{
	return 0;
}

REGISTER_FUNCTION(binomial, eval_func(binomial_eval).
                            evalf_func(binomial_evalf).
                            conjugate_func(binomial_conjugate).
                            real_part_func(binomial_real_part).
                            imag_part_func(binomial_imag_part));

//////////
// Order term function (for truncated power series)
//////////

static ex Order_eval(const ex & x)
{
	if (is_exactly_a<numeric>(x)) {
		// O(c) -> O(1) or 0
		if (!x.is_zero())
			return Order(_ex1).hold();
		else
			return _ex0;
	} else if (is_exactly_a<mul>(x)) {
		const mul &m = ex_to<mul>(x);
		// O(c*expr) -> O(expr)
		if (is_exactly_a<numeric>(m.op(m.nops() - 1)))
			return Order(x / m.op(m.nops() - 1)).hold();
	}
	return Order(x).hold();
}

static ex Order_series(const ex & x, const relational & r, int order, unsigned options)
{
	// Just wrap the function into a pseries object
	GINAC_ASSERT(is_a<symbol>(r.lhs()));
	const symbol &s = ex_to<symbol>(r.lhs());
	epvector new_seq { expair(Order(_ex1), numeric(std::min(x.ldegree(s), order))) };
	return pseries(r, std::move(new_seq));
}

static ex Order_conjugate(const ex & x)
{
	return Order(x).hold();
}

static ex Order_real_part(const ex & x)
{
	return Order(x).hold();
}

static ex Order_imag_part(const ex & x)
{
	if(x.info(info_flags::real))
		return 0;
	return Order(x).hold();
}

static ex Order_power(const ex & x, const ex & e)
{
	// Order(x)^e -> Order(x^e) for positive integer e
	if (is_exactly_a<numeric>(e) && e.info(info_flags::posint))
		return Order(pow(x, e));
	// NB: For negative exponents, the above could be wrong.
	// This is because series() produces Order(x^n) to denote the order where
	// it gave up. So, Order(x^n) can also be an x^(n+1) term if the x^n term
	// vanishes. In this situation, 1/Order(x^n) can also be a x^(-n-1) term.
	// Transforming it to Order(x^-n) would miss that.

	return power(Order(x), e).hold();
}

static ex Order_expl_derivative(const ex & arg, const symbol & s)
{
	return Order(arg.diff(s));
}

REGISTER_FUNCTION(Order, eval_func(Order_eval).
                         series_func(Order_series).
                         latex_name("\\mathcal{O}").
                         expl_derivative_func(Order_expl_derivative).
                         conjugate_func(Order_conjugate).
                         real_part_func(Order_real_part).
                         imag_part_func(Order_imag_part).
                         power_func(Order_power));

//////////
// Solve linear system
//////////

class symbolset {
	exset s;
	void insert_symbols(const ex &e)
	{
		if (is_a<symbol>(e)) {
			s.insert(e);
		} else {
			for (const ex &sube : e) {
				insert_symbols(sube);
			}
		}
	}
public:
	explicit symbolset(const ex &e)
	{
		insert_symbols(e);
	}
	bool has(const ex &e) const
	{
		return s.find(e) != s.end();
	}
};

ex lsolve(const ex &eqns, const ex &symbols, unsigned options)
{
	// solve a system of linear equations
	if (eqns.info(info_flags::relation_equal)) {
		if (!symbols.info(info_flags::symbol))
			throw(std::invalid_argument("lsolve(): 2nd argument must be a symbol"));
		const ex sol = lsolve(lst{eqns}, lst{symbols});
		
		GINAC_ASSERT(sol.nops()==1);
		GINAC_ASSERT(is_exactly_a<relational>(sol.op(0)));
		
		return sol.op(0).op(1); // return rhs of first solution
	}
	
	// syntax checks
	if (!(eqns.info(info_flags::list) || eqns.info(info_flags::exprseq))) {
		throw(std::invalid_argument("lsolve(): 1st argument must be a list, a sequence, or an equation"));
	}
	for (size_t i=0; i<eqns.nops(); i++) {
		if (!eqns.op(i).info(info_flags::relation_equal)) {
			throw(std::invalid_argument("lsolve(): 1st argument must be a list of equations"));
		}
	}
	if (!(symbols.info(info_flags::list) || symbols.info(info_flags::exprseq))) {
		throw(std::invalid_argument("lsolve(): 2nd argument must be a list, a sequence, or a symbol"));
	}
	for (size_t i=0; i<symbols.nops(); i++) {
		if (!symbols.op(i).info(info_flags::symbol)) {
			throw(std::invalid_argument("lsolve(): 2nd argument must be a list or a sequence of symbols"));
		}
	}
	
	// build matrix from equation system
	matrix sys(eqns.nops(),symbols.nops());
	matrix rhs(eqns.nops(),1);
	matrix vars(symbols.nops(),1);
	
	for (size_t r=0; r<eqns.nops(); r++) {
		const ex eq = eqns.op(r).op(0)-eqns.op(r).op(1); // lhs-rhs==0
		const symbolset syms(eq);
		ex linpart = eq;
		for (size_t c=0; c<symbols.nops(); c++) {
			if (!syms.has(symbols.op(c)))
				continue;
			const ex co = eq.coeff(ex_to<symbol>(symbols.op(c)),1);
			linpart -= co*symbols.op(c);
			sys(r,c) = co;
		}
		linpart = linpart.expand();
		rhs(r,0) = -linpart;
	}
	
	// test if system is linear and fill vars matrix
	const symbolset sys_syms(sys);
	const symbolset rhs_syms(rhs);
	for (size_t i=0; i<symbols.nops(); i++) {
		vars(i,0) = symbols.op(i);
		if (sys_syms.has(symbols.op(i)))
			throw(std::logic_error("lsolve: system is not linear"));
		if (rhs_syms.has(symbols.op(i)))
			throw(std::logic_error("lsolve: system is not linear"));
	}
	
	matrix solution;
	try {
		solution = sys.solve(vars,rhs,options);
	} catch (const std::runtime_error & e) {
		// Probably singular matrix or otherwise overdetermined system:
		// It is consistent to return an empty list
		return lst{};
	}
	GINAC_ASSERT(solution.cols()==1);
	GINAC_ASSERT(solution.rows()==symbols.nops());
	
	// return list of equations of the form lst{var1==sol1,var2==sol2,...}
	lst sollist;
	for (size_t i=0; i<symbols.nops(); i++)
		sollist.append(symbols.op(i)==solution(i,0));
	
	return sollist;
}

//////////
// Find real root of f(x) numerically
//////////

const numeric
fsolve(const ex& f_in, const symbol& x, const numeric& x1, const numeric& x2)
{
	if (!x1.is_real() || !x2.is_real()) {
		throw std::runtime_error("fsolve(): interval not bounded by real numbers");
	}
	if (x1==x2) {
		throw std::runtime_error("fsolve(): vanishing interval");
	}
	// xx[0] == left interval limit, xx[1] == right interval limit.
	// fx[0] == f(xx[0]), fx[1] == f(xx[1]).
	// We keep the root bracketed: xx[0]<xx[1] and fx[0]*fx[1]<0.
	numeric xx[2] = { x1<x2 ? x1 : x2,
	                  x1<x2 ? x2 : x1 };
	ex f;
	if (is_a<relational>(f_in)) {
		f = f_in.lhs()-f_in.rhs();
	} else {
		f = f_in;
	}
	const ex fx_[2] = { f.subs(x==xx[0]).evalf(),
	                    f.subs(x==xx[1]).evalf() };
	if (!is_a<numeric>(fx_[0]) || !is_a<numeric>(fx_[1])) {
		throw std::runtime_error("fsolve(): function does not evaluate numerically");
	}
	numeric fx[2] = { ex_to<numeric>(fx_[0]),
	                  ex_to<numeric>(fx_[1]) };
	if (!fx[0].is_real() || !fx[1].is_real()) {
		throw std::runtime_error("fsolve(): function evaluates to complex values at interval boundaries");
	}
	if (fx[0]*fx[1]>=0) {
		throw std::runtime_error("fsolve(): function does not change sign at interval boundaries");
	}

	// The Newton-Raphson method has quadratic convergence!  Simply put, it
	// replaces x with x-f(x)/f'(x) at each step.  -f/f' is the delta:
	const ex ff = normal(-f/f.diff(x));
	int side = 0;  // Start at left interval limit.
	numeric xxprev;
	numeric fxprev;
	do {
		xxprev = xx[side];
		fxprev = fx[side];
		ex dx_ = ff.subs(x == xx[side]).evalf();
		if (!is_a<numeric>(dx_))
			throw std::runtime_error("fsolve(): function derivative does not evaluate numerically");
		xx[side] += ex_to<numeric>(dx_);
		// Now check if Newton-Raphson method shot out of the interval 
		bool bad_shot = (side == 0 && xx[0] < xxprev) || 
				(side == 1 && xx[1] > xxprev) || xx[0] > xx[1];
		if (!bad_shot) {
			// Compute f(x) only if new x is inside the interval.
			// The function might be difficult to compute numerically
			// or even ill defined outside the interval. Also it's
			// a small optimization. 
			ex f_x = f.subs(x == xx[side]).evalf();
			if (!is_a<numeric>(f_x))
				throw std::runtime_error("fsolve(): function does not evaluate numerically");
			fx[side] = ex_to<numeric>(f_x);
		}
		if (bad_shot) {
			// Oops, Newton-Raphson method shot out of the interval.
			// Restore, and try again with the other side instead!
			xx[side] = xxprev;
			fx[side] = fxprev;
			side = !side;
			xxprev = xx[side];
			fxprev = fx[side];

			ex dx_ = ff.subs(x == xx[side]).evalf();
			if (!is_a<numeric>(dx_))
				throw std::runtime_error("fsolve(): function derivative does not evaluate numerically [2]");
			xx[side] += ex_to<numeric>(dx_);

			ex f_x = f.subs(x==xx[side]).evalf();
			if (!is_a<numeric>(f_x))
				throw std::runtime_error("fsolve(): function does not evaluate numerically [2]");
			fx[side] = ex_to<numeric>(f_x);
		}
		if ((fx[side]<0 && fx[!side]<0) || (fx[side]>0 && fx[!side]>0)) {
			// Oops, the root isn't bracketed any more.
			// Restore, and perform a bisection!
			xx[side] = xxprev;
			fx[side] = fxprev;

			// Ah, the bisection! Bisections converge linearly. Unfortunately,
			// they occur pretty often when Newton-Raphson arrives at an x too
			// close to the result on one side of the interval and
			// f(x-f(x)/f'(x)) turns out to have the same sign as f(x) due to
			// precision errors! Recall that this function does not have a
			// precision goal as one of its arguments but instead relies on
			// x converging to a fixed point. We speed up the (safe but slow)
			// bisection method by mixing in a dash of the (unsafer but faster)
			// secant method: Instead of splitting the interval at the
			// arithmetic mean (bisection), we split it nearer to the root as
			// determined by the secant between the values xx[0] and xx[1].
			// Don't set the secant_weight to one because that could disturb
			// the convergence in some corner cases!
			constexpr double secant_weight = 0.984375;  // == 63/64 < 1
			numeric xxmid = (1-secant_weight)*0.5*(xx[0]+xx[1])
			    + secant_weight*(xx[0]+fx[0]*(xx[0]-xx[1])/(fx[1]-fx[0]));
			ex fxmid_ = f.subs(x == xxmid).evalf();
			if (!is_a<numeric>(fxmid_))
				throw std::runtime_error("fsolve(): function does not evaluate numerically [3]");
			numeric fxmid = ex_to<numeric>(fxmid_);
			if (fxmid.is_zero()) {
				// Luck strikes...
				return xxmid;
			}
			if ((fxmid<0 && fx[side]>0) || (fxmid>0 && fx[side]<0)) {
				side = !side;
			}
			xxprev = xx[side];
			fxprev = fx[side];
			xx[side] = xxmid;
			fx[side] = fxmid;
		}
	} while (xxprev!=xx[side]);
	return xxprev;
}


/* Force inclusion of functions from inifcns_gamma and inifcns_zeta
 * for static lib (so ginsh will see them). */
unsigned force_include_tgamma = tgamma_SERIAL::serial;
unsigned force_include_zeta1 = zeta1_SERIAL::serial;






///This function is used in evalf functions of the integral functions.
///
ex integral_evalf(const ex& x, const std::string& integralFuncname)
{
    //if(!x.info(info_flags::real)){
        arb_t xreal, ximag;
        arb_init(xreal);
        arb_init(ximag);
        arb_set_str(xreal,to_string(x.real_part()).c_str(),_digits);
        arb_set_str(ximag,to_string(x.imag_part()).c_str(),_digits);

        acb_t xf,value;
        acb_init(xf);
        acb_init(value);
        acb_set_arb_arb(xf,xreal,ximag);
        arb_clear(xreal);
        arb_clear(ximag);

        if(integralFuncname=="Si"){
            acb_hypgeom_si(value,xf,_digits);
        }
        else if(integralFuncname=="Ci"){
            acb_hypgeom_ci(value,xf,_digits);
        }
        else if(integralFuncname=="Shi"){
            acb_hypgeom_shi(value,xf,_digits);
        }
        else if(integralFuncname=="Chi"){
            acb_hypgeom_chi(value,xf,_digits);
        }
        else if(integralFuncname=="li"){
            acb_hypgeom_li(value,xf,0,_digits);
        }
        else if(integralFuncname=="Ei"){
            acb_hypgeom_ei(value,xf,_digits);
        }

        acb_clear(xf);

        arb_t real,imag;
        arb_init(real);
        arb_init(imag);
        acb_get_real(real,value);
        acb_get_imag(imag,value);
        std::string realstr=arb_get_str(real,_digits,ARB_STR_NO_RADIUS);
        std::string imagstr=arb_get_str(imag,_digits,ARB_STR_NO_RADIUS);
        if(arb_is_int(real))//for avoiding unwanting zero after decimal point of exact integer
            realstr=realstr.substr(0,realstr.find("."));
        if(arb_is_int(imag))//for avoiding unwanting zero after decimal point of exact integer
            imagstr=imagstr.substr(0,imagstr.find("."));
        arb_clear(real);
        arb_clear(imag);
        acb_clear(value);
        flint_cleanup_master();

        if(realstr=="nan" || imagstr=="nan")
            return externSymbols.nan;
        else
            return  generator.exGeneratorFromString((realstr+"+I*"+imagstr).c_str());
    //}
//    else{
//        arb_t xreal;
//        arb_init(xreal);
//        arb_set_str(xreal,to_string(x.real_part()).c_str(),_digits);

//        arb_t value;
//        arb_init(value);

//        if(integralFuncname=="Si"){
//            arb_hypgeom_si(value,xreal,_digits);
//        }
//        else if(integralFuncname=="Ci"){
//            arb_hypgeom_ci(value,xreal,_digits);
//        }
//        else if(integralFuncname=="Shi"){
//            arb_hypgeom_shi(value,xreal,_digits);
//        }
//        else if(integralFuncname=="Chi"){
//            arb_hypgeom_chi(value,xreal,_digits);
//        }
//        else if(integralFuncname=="Ei"){
//            arb_hypgeom_ei(value,xreal,_digits);
//        }
//        else if(integralFuncname=="li"){
//            arb_hypgeom_li(value,xreal,0,_digits);
//        }

//        arb_clear(xreal);

//        std::string realstr=arb_get_str(value,_digits,ARB_STR_NO_RADIUS);
//        if(arb_is_int(value))//for avoiding unwanting zero after decimal point of exact integer
//            realstr=realstr.substr(0,realstr.find("."));
//        arb_clear(value);
//        flint_cleanup_master();

//        return  numeric((realstr).c_str());
//    }

}


//////////
// sin integral (Si)
//////////

static ex si_evalf(const ex & x)
{
    if (is_exactly_a<numeric>(x))
    {
        return integral_evalf(x,"Si");
    }

    return sinIntegral(x).hold();
}

static ex si_eval(const ex & x)
{
    if (is_exactly_a<numeric>(x) and !x.info(info_flags::crational)){

        return sinIntegral(x).evalf();
    }

    return sinIntegral(x).hold();
}

static ex si_deriv(const ex & x, unsigned deriv_param)
{
    GINAC_ASSERT(deriv_param==0);
    return sin(x)/x;
}


REGISTER_FUNCTION(sinIntegral, eval_func(si_eval).
                        evalf_func(si_evalf).
                        derivative_func(si_deriv).
                        latex_name( "\\text{Si}"));


//////////
// cosine integral (Ci)
//////////

static ex ci_evalf(const ex & x)
{
    if (is_exactly_a<numeric>(x))
    {
        return integral_evalf(x,"Ci");
    }

    return cosIntegral(x).hold();
}

static ex ci_eval(const ex & x)
{
    if (is_exactly_a<numeric>(x) and !x.info(info_flags::crational))
        return cosIntegral(x).evalf();

    return cosIntegral(x).hold();
}

static ex ci_deriv(const ex & x, unsigned deriv_param)
{
    GINAC_ASSERT(deriv_param==0);
    return cos(x)/x;
}


REGISTER_FUNCTION(cosIntegral, eval_func(ci_eval).
                               evalf_func(ci_evalf).
                               derivative_func(ci_deriv).
                               latex_name( "\\text{Ci}"));

//////////
// sinh integral (Sih)
//////////

static ex sih_evalf(const ex & x)
{
    if (is_exactly_a<numeric>(x))
    {
        return integral_evalf(x,"Sih");
    }

    return sinhIntegral(x).hold();
}

static ex sih_eval(const ex & x)
{
    if (is_exactly_a<numeric>(x) and !x.info(info_flags::crational))
        return sinhIntegral(x).evalf();

    return sinhIntegral(x).hold();
}

static ex sih_deriv(const ex & x, unsigned deriv_param)
{
    GINAC_ASSERT(deriv_param==0);
    return sinh(x)/x;
}


REGISTER_FUNCTION(sinhIntegral, eval_func(sih_eval).
                               evalf_func(sih_evalf).
                               derivative_func(sih_deriv).
                               latex_name( "\\text{Sih}"));


//////////
// cosh integral (Cih)
//////////

static ex cih_evalf(const ex & x)
{
    if (is_exactly_a<numeric>(x))
    {
        return integral_evalf(x,"Cih");
    }

    return coshIntegral(x).hold();
}

static ex cih_eval(const ex & x)
{
    if (is_exactly_a<numeric>(x) and !x.info(info_flags::crational))
        return coshIntegral(x).evalf();

    return coshIntegral(x).hold();
}

static ex cih_deriv(const ex & x, unsigned deriv_param)
{
    GINAC_ASSERT(deriv_param==0);
    return cosh(x)/x;
}


REGISTER_FUNCTION(coshIntegral, eval_func(cih_eval).
                               evalf_func(cih_evalf).
                               derivative_func(cih_deriv).
                               latex_name( "\\text{Cih}"));


//////////
// log integral (li)
//////////

static ex li_evalf(const ex & x)
{
    if (is_exactly_a<numeric>(x))
    {
        return integral_evalf(x,"li");
    }

    return logIntegral(x).hold();
}

static ex li_eval(const ex & x)
{
    if (is_exactly_a<numeric>(x) and !x.info(info_flags::crational))
        return logIntegral(x).evalf();

    return logIntegral(x).hold();
}

static ex li_deriv(const ex & x, unsigned deriv_param)
{
    GINAC_ASSERT(deriv_param==0);
    return 1/log(x);
}


REGISTER_FUNCTION(logIntegral, eval_func(li_eval).
                                evalf_func(li_evalf).
                                derivative_func(li_deriv).
                                latex_name( "\\text{li}"));

//////////
// Exponential integral (Ei)
//////////

static ex ei_evalf(const ex & x)
{
    if (is_exactly_a<numeric>(x))
    {
        return integral_evalf(x,"Ei");
    }

    return expIntegralEi(x).hold();
}

static ex ei_eval(const ex & x)
{
    if (is_exactly_a<numeric>(x) and !x.info(info_flags::crational))
        return expIntegralEi(x).evalf();

    return expIntegralEi(x).hold();
}

static ex ei_deriv(const ex & x, unsigned deriv_param)
{
    GINAC_ASSERT(deriv_param==0);
    return exp(x)/x;
}


REGISTER_FUNCTION(expIntegralEi, eval_func(ei_eval).
                                evalf_func(ei_evalf).
                                derivative_func(ei_deriv).
                                latex_name( "\\text{Ei}"));

//////////
// generalized exponential integral (E(s,x))
//////////

static ex gei_evalf(const ex & s, const ex & x)
{
    if (is_exactly_a<numeric>(s) and is_exactly_a<numeric>(x))
    {
        //if(!s.info(info_flags::real) || !x.info(info_flags::real)){
            arb_t nreal, nimag,xreal, ximag;
            arb_init(nreal);
            arb_init(nimag);
            arb_set_str(nreal,to_string(s.real_part()).c_str(),_digits);
            arb_set_str(nimag,to_string(s.imag_part()).c_str(),_digits);
            arb_init(xreal);
            arb_init(ximag);
            arb_set_str(xreal,to_string(x.real_part()).c_str(),_digits);
            arb_set_str(ximag,to_string(x.imag_part()).c_str(),_digits);

            acb_t nf,xf,value;
            acb_init(nf);
            acb_init(xf);
            acb_init(value);
            acb_set_arb_arb(nf,nreal,nimag);
            acb_set_arb_arb(xf,xreal,ximag);
            acb_clear(value);
            arb_clear(nreal);
            arb_clear(nimag);
            arb_clear(xreal);
            arb_clear(ximag);

            acb_hypgeom_expint(value,nf,xf,_digits);

            acb_clear(nf);
            acb_clear(xf);

            arb_t real,imag;
            arb_init(real);
            arb_init(imag);
            acb_get_real(real,value);
            acb_get_imag(imag,value);
            std::string realstr=arb_get_str(real,_digits,ARB_STR_NO_RADIUS);
            std::string imagstr=arb_get_str(imag,_digits,ARB_STR_NO_RADIUS);
            if(arb_is_int(real))//for avoiding unwanting zero after decimal point of exact integer
                realstr=realstr.substr(0,realstr.find("."));
            if(arb_is_int(imag))//for avoiding unwanting zero after decimal point of exact integer
                imagstr=imagstr.substr(0,imagstr.find("."));
            arb_clear(real);
            arb_clear(imag);
            acb_clear(value);
            flint_cleanup_master();

            if(realstr=="nan" || imagstr=="nan")
                return externSymbols.nan;
            else
                return  generator.exGeneratorFromString((realstr+"+I*"+imagstr).c_str());
        //}

//        else{
//            arb_t nreal,xreal;
//            arb_init(nreal);
//            arb_set_str(nreal,to_string(s.real_part()).c_str(),_digits);
//            arb_init(xreal);
//            arb_set_str(xreal,to_string(x.real_part()).c_str(),_digits);

//            arb_t value;
//            arb_init(value);
//            arb_hypgeom_expint(value,nreal,xreal,_digits);
//            arb_clear(nreal);
//            arb_clear(xreal);

//            std::string realstr=arb_get_str(value,_digits,ARB_STR_NO_RADIUS);
//            if(arb_is_int(value))//for avoiding unwanting zero after decimal point of exact integer
//                realstr=realstr.substr(0,realstr.find("."));
//            arb_clear(value);
//            flint_cleanup_master();

//            return  numeric((realstr).c_str());
//        }
    }

    return expIntegralE(s,x).hold();
}

static ex gei_eval(const ex & s, const ex & x)
{
    if (is_exactly_a<numeric>(s)
        and is_exactly_a<numeric>(x)
        and (!ex_to<numeric>(s).info(info_flags::crational)
             or !ex_to<numeric>(x).info(info_flags::crational)))
        return expIntegralE(s,x).evalf();

    return expIntegralE(s,x).hold();
}

static ex gei_deriv(const ex & s, const ex & x, unsigned deriv_param)
{
    GINAC_ASSERT(deriv_param==0);
    return -expIntegralE(s-1,x);
}

static void gei_print_latex(const ex& s, const ex & x, const print_context & c)
{
    c.s << "\\text{E}_"; s.print(c);c.s<<"(";x.print(c); c.s << ")";
}

REGISTER_FUNCTION(expIntegralE, eval_func(gei_eval).
                                 evalf_func(gei_evalf).
                                 derivative_func(gei_deriv).
                                 print_func<print_latex>(gei_print_latex));





///This function is used in evalf functions of the special functions.
///
ex special_evalf(const ex& n, const ex& m, const ex& x, const std::string& specialfuncname)
{
    //if(!n.info(info_flags::real) || !m.info(info_flags::real) || !x.info(info_flags::real)){
        arb_t nreal, nimag,xreal, ximag;
        arb_init(nreal);
        arb_init(nimag);
        arb_set_str(nreal,to_string(n.real_part()).c_str(),_digits);
        arb_set_str(nimag,to_string(n.imag_part()).c_str(),_digits);
        arb_init(xreal);
        arb_init(ximag);
        arb_set_str(xreal,to_string(x.real_part()).c_str(),_digits);
        arb_set_str(ximag,to_string(x.imag_part()).c_str(),_digits);

        acb_t nf,xf,value;
        acb_init(nf);
        acb_init(xf);
        acb_init(value);
        acb_set_arb_arb(nf,nreal,nimag);
        acb_set_arb_arb(xf,xreal,ximag);
        arb_clear(nreal);
        arb_clear(nimag);
        arb_clear(xreal);
        arb_clear(ximag);

        if(specialfuncname=="chebyshevT"){
            acb_hypgeom_chebyshev_t(value,nf,xf,_digits);
        }
        else if(specialfuncname=="chebyshevU"){
            acb_hypgeom_chebyshev_u(value,nf,xf,_digits);
        }
        else if(specialfuncname=="legendreP"){
            acb_t mf;
            arb_t mreal, mimag;
            acb_init(mf);
            arb_init(mreal);
            arb_init(mimag);
            arb_set_str(mreal,to_string(m.real_part()).c_str(),_digits);
            arb_set_str(mimag,to_string(m.imag_part()).c_str(),_digits);
            acb_set_arb_arb(mf,mreal,mimag);
            acb_hypgeom_legendre_p(value,nf,mf,xf,0,_digits);
            arb_clear(mreal);
            arb_clear(mimag);
            acb_clear(mf);
        }
        else if(specialfuncname=="legendreQ"){
            acb_t mf;
            arb_t mreal, mimag;
            acb_init(mf);
            arb_init(mreal);
            arb_init(mimag);
            arb_set_str(mreal,to_string(m.real_part()).c_str(),_digits);
            arb_set_str(mimag,to_string(m.imag_part()).c_str(),_digits);
            acb_set_arb_arb(mf,mreal,mimag);
            acb_hypgeom_legendre_q(value,nf,mf,xf,0,_digits);
            arb_clear(mreal);
            arb_clear(mimag);
            acb_clear(mf);
        }
        else if(specialfuncname=="besselJ"){
            acb_hypgeom_bessel_j(value,nf,xf,_digits);
        }
        else if(specialfuncname=="besselY"){
            acb_hypgeom_bessel_y(value,nf,xf,_digits);
        }
        else if(specialfuncname=="besselI"){
            acb_hypgeom_bessel_i(value,nf,xf,_digits);
        }
        else if(specialfuncname=="besselK"){
            acb_hypgeom_bessel_k(value,nf,xf,_digits);
        }
        else if(specialfuncname=="hermiteH"){
            acb_hypgeom_hermite_h(value,nf,xf,_digits);
        }
        else if(specialfuncname=="gegenbauerC"){
            acb_t mf;
            arb_t mreal, mimag;
            acb_init(mf);
            arb_init(mreal);
            arb_init(mimag);
            arb_set_str(mreal,to_string(m.real_part()).c_str(),_digits);
            arb_set_str(mimag,to_string(m.imag_part()).c_str(),_digits);
            acb_set_arb_arb(mf,mreal,mimag);
            acb_hypgeom_gegenbauer_c(value,nf,mf,xf,_digits);
            arb_clear(mreal);
            arb_clear(mimag);
            acb_clear(mf);
        }
        acb_clear(nf);
        acb_clear(xf);

        arb_t real,imag;
        arb_init(real);
        arb_init(imag);
        acb_get_real(real,value);
        acb_get_imag(imag,value);
        std::string realstr=arb_get_str(real,_digits,ARB_STR_NO_RADIUS);
        std::string imagstr=arb_get_str(imag,_digits,ARB_STR_NO_RADIUS);
        if(arb_is_int(real))//for avoiding unwanting zero after decimal point of exact integer
            realstr=realstr.substr(0,realstr.find("."));
        if(arb_is_int(imag))//for avoiding unwanting zero after decimal point of exact integer
            imagstr=imagstr.substr(0,imagstr.find("."));
        arb_clear(real);
        arb_clear(imag);
        acb_clear(value);
        flint_cleanup_master();

    if(realstr=="nan" || imagstr=="nan")
        return externSymbols.nan;
    else
        return  generator.exGeneratorFromString((realstr+"+I*"+imagstr).c_str());
    //}
//    else{
//        arb_t nreal,xreal;
//        arb_init(nreal);
//        arb_set_str(nreal,to_string(n.real_part()).c_str(),_digits);
//        arb_init(xreal);
//        arb_set_str(xreal,to_string(x.real_part()).c_str(),_digits);

//        arb_t value;
//        arb_init(value);
//        if(specialfuncname=="chebyshevT"){
//            arb_hypgeom_chebyshev_t(value,nreal,xreal,_digits);
//        }
//        else if(specialfuncname=="chebyshevU"){
//            arb_hypgeom_chebyshev_u(value,nreal,xreal,_digits);
//        }
//        else if(specialfuncname=="legendreP"){
//            arb_t mreal;
//            arb_init(mreal);
//            arb_set_str(mreal,to_string(m).c_str(),_digits);
//            arb_hypgeom_legendre_p(value,nreal,mreal,xreal,0,_digits);
//            arb_clear(mreal);
//        }
//        else if(specialfuncname=="legendreQ"){
//            arb_t mreal;
//            arb_init(mreal);
//            arb_set_str(mreal,to_string(m).c_str(),_digits);
//            arb_hypgeom_legendre_q(value,nreal,mreal,xreal,0,_digits);
//            arb_clear(mreal);
//        }
//        else if(specialfuncname=="besselJ"){
//            arb_hypgeom_bessel_j(value,nreal,xreal,_digits);
//        }
//        else if(specialfuncname=="besselY"){
//            arb_hypgeom_bessel_y(value,nreal,xreal,_digits);
//        }
//        else if(specialfuncname=="besselI"){
//            arb_hypgeom_bessel_i(value,nreal,xreal,_digits);
//        }
//        else if(specialfuncname=="besselK"){
//            arb_hypgeom_bessel_k(value,nreal,xreal,_digits);
//        }
//        else if(specialfuncname=="hermiteH"){
//            arb_hypgeom_hermite_h(value,nreal,xreal,_digits);
//        }
//        else if(specialfuncname=="gegenbauerC"){
//            arb_t mreal;
//            arb_init(mreal);
//            arb_set_str(mreal,to_string(m).c_str(),_digits);
//            arb_hypgeom_gegenbauer_c(value,nreal,mreal,xreal,_digits);
//            arb_clear(mreal);
//        }
//        arb_clear(nreal);
//        arb_clear(xreal);

//        std::string realstr=arb_get_str(value,_digits,ARB_STR_NO_RADIUS);
//        if(arb_is_int(value))//for avoiding unwanting zero after decimal point of exact integer
//            realstr=realstr.substr(0,realstr.find("."));
//        arb_clear(value);
//        flint_cleanup_master();
//                    std::cout<<realstr <<std::endl;
//        return  numeric((realstr).c_str());
//    }

}


//////////
// Chebyshev polynomials T_n(x)
//////////
static ex chebyt_evalf(const ex& n, const ex& x)
{
    if (not is_exactly_a<numeric>(x)
        or not is_exactly_a<numeric>(n))
        return chebyshevT(n,x).hold();

    return special_evalf(n,_ex0,x,"chebyshevT");
}


static ex chebyt_eval(const ex& n_, const ex& x)
{
        if (is_exactly_a<numeric>(n_)
            and is_exactly_a<numeric>(x)
            and (!ex_to<numeric>(n_).info(info_flags::crational)
                 or !ex_to<numeric>(x).info(info_flags::crational)))
                return chebyshevT(n_, x).evalf();

        if (x.is_equal(_ex1))
                return x;
        if (x.is_equal(_ex_1))
                return power(x, n_);
        if (x.is_zero())
                return cos(Pi*n_/_ex2);
        if (not is_exactly_a<numeric>(n_)
            or not n_.info(info_flags::integer))
                return chebyshevT(n_, x).hold();

        numeric numn = ex_to<numeric>(n_);
        if (numn.is_zero())
                return _ex1;
        if (numn.is_equal(1))
                return x;
        if (numn.info(info_flags::negative))
                numn = -numn;
        //epvector vec;
        fmpz_poly_t p;
        fmpz_poly_init(p);
        fmpz_poly_chebyshev_t(p, static_cast<ulong>(numn.to_long()));
        if(!is_number(x)){
            const std::string strPoly=fmpz_poly_get_str_pretty(p, to_string(externSymbols.symb_).c_str());
            fmpz_poly_clear(p);
            flint_cleanup_master();
            return  generator.exGeneratorFromString(strPoly).subs(externSymbols.symb_==x);
        }
        else if(x.info(info_flags::crational)){
            fmpq_t pValue;
            fmpq_t xPoint;
            fmpq_init(pValue);
            fmpq_init(xPoint);
            fmpq_set_str(xPoint,to_string(x).c_str(),10);
            fmpz_poly_evaluate_fmpq(pValue,p,xPoint);
            const std::string str= fmpq_get_str(NULL,10,pValue);
            fmpz_poly_clear(p);
            fmpq_clear(xPoint);
            fmpq_clear(pValue);
            flint_cleanup_master();
            return  numeric(str.c_str());
        }

        //std::cout<<"pp "<<std::endl;
        return  chebyshevT(n_, x).hold();
//        int len = fmpz_poly_length(p);
//        ex currx = _ex1;
//        for (int i = 0; i<len; ++i) {
//                mpz_t bigint;
//                mpz_init(bigint);
//                fmpz_poly_get_coeff_mpz(bigint, p, i);
//                numeric coeff(bigint);
//                if (not coeff.is_zero())
//                        vec.emplace_back(currx, coeff);
//                currx *= x;
//        }
//        return add(vec);
}

static ex chebyt_deriv(const ex& n, const ex & x, unsigned deriv_param)
{
	    if (deriv_param == 0)
                    throw std::runtime_error("derivative w.r.t. to the index is not supported yet");
        return n * chebyshevU(n-_ex1, x).hold();
}

static void chebyt_print_latex(const ex& n, const ex & x, const print_context & c)
{
    c.s << "\\text{T}_{"; n.print(c);c.s<<"}(";x.print(c); c.s << ")";
}

REGISTER_FUNCTION(chebyshevT, evalf_func(chebyt_evalf).
                               eval_func(chebyt_eval).
                               derivative_func(chebyt_deriv).
                              print_func<print_latex>(chebyt_print_latex));

//////////
// Chebyshev polynomials U_n(x)
//////////
static ex chebyu_evalf(const ex& n, const ex& x)
{
    if (not is_exactly_a<numeric>(x)
        or not is_exactly_a<numeric>(n))
        return chebyshevU(n,x).hold();

    return special_evalf(n,_ex0,x,"chebyshevU");

    //fmpq_poly_legendre_p(fmpq_poly_t poly, ulong n)
    // see http://dlmf.nist.gov/15.9.E7
    //        const numeric& numn = ex_to<numeric>(n);
    //        const numeric& numx = ex_to<numeric>(x);
    //        std::vector<numeric> numveca, numvecb;
    //        numveca.push_back(-numn);
    //        numveca.push_back(numn + *_num1_p);
    //        numvecb.push_back(*_num1_p);
    //        return hypergeometric_pFq(numveca, numvecb, (*_num1_p - numx).mul(*_num1_2_p));
}

static ex chebyu_eval(const ex& n_, const ex& x)
{
        if (is_exactly_a<numeric>(n_)
            and is_exactly_a<numeric>(x)
            and (!ex_to<numeric>(n_).info(info_flags::crational)
                 or !ex_to<numeric>(x).info(info_flags::crational)))
                return chebyshevU(n_, x).evalf();

        if (x.is_equal(_ex1))
                return n_ + _ex1;
        if (x.is_equal(_ex_1))
                return power(_ex_1, n_) * (n_+_ex1);
        if (x.is_zero())
                return cos(Pi*n_/_ex2);
        if (not is_exactly_a<numeric>(n_)
            or not n_.info(info_flags::integer))
                return chebyshevU(n_, x).hold();

        const numeric& numn = ex_to<numeric>(n_);
        if (numn.is_zero())
                return _ex1;
        if (numn.is_equal(1))
                return mul(x, _ex2);
        if (numn.info(info_flags::negative))
                return -chebyu_eval(-numn-*_num2_p, x);

        //epvector vec;
        fmpz_poly_t p;
        fmpz_poly_init(p);
        fmpz_poly_chebyshev_u(p, static_cast<ulong>(numn.to_long()));
        if(!is_number(x)){
            const std::string strPoly=fmpz_poly_get_str_pretty(p, to_string(externSymbols.symb_).c_str());
            fmpz_poly_clear(p);
            flint_cleanup_master();
            return  generator.exGeneratorFromString(strPoly).subs(externSymbols.symb_==x);
        }
        else if(x.info(info_flags::crational)){
            fmpq_t pValue;
            fmpq_t xPoint;
            fmpq_init(pValue);
            fmpq_init(xPoint);
            fmpq_set_str(xPoint,to_string(x).c_str(),10);
            fmpz_poly_evaluate_fmpq(pValue,p,xPoint);
            const std::string str= fmpq_get_str(NULL,10,pValue);
            fmpz_poly_clear(p);
            fmpq_clear(xPoint);
            fmpq_clear(pValue);
            flint_cleanup_master();
            return  numeric(str.c_str());
        }

        return  chebyshevU(n_, x).hold();

//        int len = fmpz_poly_length(p);
//        ex currx = _ex1;
//        for (int i = 0; i<len; ++i) {
//                mpz_t bigint;
//                mpz_init(bigint);
//                fmpz_poly_get_coeff_mpz(bigint, p, i);
//                numeric coeff(bigint);
//                if (not coeff.is_zero())
//                        vec.emplace_back(currx, coeff);
//                currx *= x;
//        }
//        fmpz_poly_clear(p);
//        return add(vec);
}

static ex chebyu_deriv(const ex& n, const ex & x, unsigned deriv_param)
{
	    if (deriv_param == 0)
                    throw std::runtime_error("derivative w.r.t. to the index is not supported yet");
        return ((n+1) * chebyshevT(n+_ex1, x).hold() - x*chebyshevU(n, x)) / (power(x, 2) - _ex1);
}

static void chebyu_print_latex(const ex& n, const ex & x, const print_context & c)
{
    c.s << "\\text{U}_{"; n.print(c);c.s<<"}(";x.print(c); c.s << ")";
}

REGISTER_FUNCTION(chebyshevU, evalf_func(chebyu_evalf).
                               eval_func(chebyu_eval).
                               derivative_func(chebyu_deriv).
                              print_func<print_latex>(chebyu_print_latex));

//////////
// Legendre polynomials P_n(x)
//////////

static ex legp_evalf(const ex& n, const ex& x)
{
	if (not is_exactly_a<numeric>(x)
             or not is_exactly_a<numeric>(n))
        return legendreP(n,x).hold();

    return special_evalf(n,_ex0,x,"legendreP");
        //fmpq_poly_legendre_p(fmpq_poly_t poly, ulong n)
        // see http://dlmf.nist.gov/15.9.E7
//        const numeric& numn = ex_to<numeric>(n);
//        const numeric& numx = ex_to<numeric>(x);
//        std::vector<numeric> numveca, numvecb;
//        numveca.push_back(-numn);
//        numveca.push_back(numn + *_num1_p);
//        numvecb.push_back(*_num1_p);
//        return hypergeometric_pFq(numveca, numvecb, (*_num1_p - numx).mul(*_num1_2_p));
}

static ex legp_eval(const ex& n_, const ex& x)
{
    if (is_exactly_a<numeric>(n_)
        and is_exactly_a<numeric>(x)
        and (!ex_to<numeric>(n_).info(info_flags::crational)
             or !ex_to<numeric>(x).info(info_flags::crational)))
        return legendreP(n_, x).evalf();

    ex n;
    if (n_.info(info_flags::negative))
            n = _ex_1 - n_;
    else
            n = n_;

    if (not is_exactly_a<numeric>(n)
        or not n.info(info_flags::integer))
            return legendreP(n, x).hold();

        const numeric& numn = ex_to<numeric>(n);
        if (numn.is_zero())
                return _ex1;
        if (numn.is_equal(1))
                return x;

    unsigned long d, k, L;
    unsigned long n_long = static_cast<unsigned long>(numn.to_long());
    d = k = n_long >> 1;

    while (k)
    {
            k >>= 1;
            d += k;
    }
    numeric den = _num2_p->pow_intexp(d);
    L = n_long / 2;
    unsigned int odd = n_long % 2;
    unsigned long index = odd;
    numeric curr_coeff = binomial(numn, numeric(L));
    curr_coeff *= den;
    if (odd)
            curr_coeff *= L + 1;
    curr_coeff /= _num2_p->pow_intexp(2*L);
    if (L % 2)
            curr_coeff = -curr_coeff;

    epvector vec;
    vec.emplace_back(power(x, numeric(index)), curr_coeff / den);
    for (k = 1; k <= L; k++)
    {
            curr_coeff *= L + 1 - k;
            curr_coeff *= 2*k + 2*L - 1 + 2*odd;
            curr_coeff /= k;
            curr_coeff /= 2*k - 1 + 2*odd;
            curr_coeff = -curr_coeff;
            index += 2;
            vec.emplace_back(power(x, numeric(index)), curr_coeff / den);
    }

    return add(vec);
}

static ex legp_deriv(const ex& n, const ex & x, unsigned deriv_param)
{
	    if (deriv_param == 0)
                    throw std::runtime_error("derivative w.r.t. to the index is not supported yet");
        return (n*legendreP(n-1, x).hold() - n*x*legendreP(n, x).hold()) / (1 - pow(x, 2));
}


static void legp_print_latex(const ex& n, const ex & x, const print_context & c)
{
    c.s << "\\text{P}_{"; n.print(c);c.s<<"}(";x.print(c); c.s << ")";
}

unsigned legendreP2_SERIAL::serial = function::register_new(function_options("legendreP", 2).
                                                           eval_func(legp_eval).
                                                           evalf_func(legp_evalf).
                                                           derivative_func(legp_deriv).
                                                           print_func<print_latex>(legp_print_latex).
                                                           do_not_evalf_params().
                                                           overloaded(2));
//////////
// Legendre functions Q_n(x) (second kind)
//////////
static ex legq_evalf(const ex& n, const ex& x)
{
    if (not is_exactly_a<numeric>(x)
        or not is_exactly_a<numeric>(n))
        return legendreQ(n,x).hold();

    return special_evalf(n,_ex0,x,"legendreQ");
}

static ex legq_eval(const ex& n_, const ex& x)
{
    if (is_exactly_a<numeric>(n_)
        and is_exactly_a<numeric>(x)
        and (!ex_to<numeric>(n_).info(info_flags::crational)
             or !ex_to<numeric>(x).info(info_flags::crational)))
        return legendreQ(n_, x).evalf();

    if (not is_exactly_a<numeric>(n_)
        or not n_.info(info_flags::integer))
        return legendreQ(n_, x).hold();

    if (n_.info(info_flags::negative))
        return Infinity;
    if(x.info(info_flags::numeric))
        return subs(legendreQ(n_,externSymbols.symb_),externSymbols.symb_==x);
    //Bonnet's recursion formula
    if (n_.is_equal(_ex0)) {
        return _ex1_2*log((_ex1+x)/(_ex1-x));
    }
    else if(n_.is_equal(_ex1)){
        return legendreP(1,x)*legendreQ(0,x)-_ex1;
    }
    else{
        return ((2*n_-1)/n_)*x*legendreQ(n_-1,x)-((n_-1)/n_)*legendreQ(n_-2,x);
    }


}

static ex legq_deriv(const ex& n, const ex & x, unsigned deriv_param)
{
    if (deriv_param == 0)
        throw std::runtime_error("derivative w.r.t. to the index is not supported yet");
//    if(!n.info(info_flags::numeric))
//        return Diff(legendreQ(n, x).hold(),x);
    return (n*legendreQ(n-1, x).hold() - n*x*legendreQ(n, x).hold()) / (1 - pow(x, 2));
}

static void legq_print_latex(const ex& n, const ex & x, const print_context & c)
{
    c.s << "\\text{Q}_{"; n.print(c);c.s<<"}(";x.print(c); c.s << ")";
}


unsigned legendreQ2_SERIAL::serial = function::register_new(function_options("legendreQ", 2).
                                                        eval_func(legq_eval).
                                                        evalf_func(legq_evalf).
                                                        derivative_func(legq_deriv).
                                                        print_func<print_latex>(legq_print_latex).
                                                        do_not_evalf_params().
                                                        overloaded(2));


//////////
// associated Legendre polynomials P^m_n(x)
//////////
static ex legpm_evalf(const ex& m, const ex& n, const ex& x)
{
    if (not is_exactly_a<numeric>(n)
        or not is_exactly_a<numeric>(m)
        or not is_exactly_a<numeric>(x))
        return legendreP(n,m,x).hold();

    return special_evalf(n,m,x,"legendreP");
}

static ex legpm_eval(const ex& m, const ex& n, const ex& x)
{
    if (is_exactly_a<numeric>(n)
        and is_exactly_a<numeric>(m)
        and is_exactly_a<numeric>(x)
        and (!ex_to<numeric>(n).info(info_flags::crational)
             or !ex_to<numeric>(m).info(info_flags::crational)
             or !ex_to<numeric>(x).info(info_flags::crational)))
        return legendreP(n,m, x).evalf();

    if(!n.info(info_flags::integer))
        return legendreP(n,m,x).hold();
    if(!m.info(info_flags::integer))
        return legendreP(n,m,x).hold();
    if(x.info(info_flags::numeric))
        return subs(legendreP(n,m,externSymbols.symb_),externSymbols.symb_==x);
    if (m.info(info_flags::positive)) {
        return pow(-1,m)*pow(1-x*x,m/2)*legendreP(n,x).diff(ex_to<symbol>(x),ex_to<numeric>(m).to_int());
    }
    else
        return pow(-1,2*m)*(factorial(n-m)/factorial(n+m))*pow(1-x*x,m/2)*legendreP(n,x).diff(ex_to<symbol>(x),ex_to<numeric>(m).to_int());
}

static ex legpm_deriv(const ex& m, const ex& n, const ex & x, unsigned deriv_param)
{
    if (deriv_param == 0)
        throw std::runtime_error("derivative w.r.t. to the index is not supported yet");
    return pow(( ( -1 + pow(( x ),( 2 )) ) ),( -1 )) * ( ( -1 + -1 * n ) * x * legendreP(n,m,x) + ( 1 + ( -1 * m + n ) ) * legendreP(1+n,m,x) );
}

static void legpm_print_latex(const ex& m, const ex & n, const ex & x, const print_context & c)
{
    c.s << "\\text{P}_{"; n.print(c);c.s<<"}^{";m.print(c);c.s<<"}(";x.print(c); c.s << ")";
}

unsigned legendreP3_SERIAL::serial = function::register_new(function_options("legendreP", 3).
                                                            eval_func(legpm_eval).
                                                            evalf_func(legpm_evalf).
                                                            derivative_func(legpm_deriv).
                                                            print_func<print_latex>(legpm_print_latex).
                                                            do_not_evalf_params().
                                                            overloaded(2));


//////////
// associated Legendre functions Q^m_n(x)
//////////
static ex legqm_evalf(const ex& m, const ex& n, const ex& x)
{
    if (not is_exactly_a<numeric>(n)
        or not is_exactly_a<numeric>(m)
        or not is_exactly_a<numeric>(x))
        return legendreQ(n,m,x).hold();

    return special_evalf(n,m,x,"legendreQ");
}

static ex legqm_eval(const ex& m, const ex& n, const ex& x)
{
    if (is_exactly_a<numeric>(n)
        and is_exactly_a<numeric>(m)
        and is_exactly_a<numeric>(x)
        and (!ex_to<numeric>(n).info(info_flags::crational)
             or !ex_to<numeric>(m).info(info_flags::crational)
             or !ex_to<numeric>(x).info(info_flags::crational)))
        return legendreQ(n,m, x).evalf();

    if(!n.info(info_flags::integer))
        return legendreQ(n,m,x).hold();
    if(!m.info(info_flags::integer))
        return legendreQ(n,m,x).hold();
    if(n.info(info_flags::negative) and m.info(info_flags::negative))
        return Infinity;
    if(x.info(info_flags::numeric))
        return subs(legendreQ(n,m,externSymbols.symb_),externSymbols.symb_==x);
    if (m.info(info_flags::positive)) {
        return pow(-1,m)*pow(1-x*x,m/2)*legendreQ(n,x).diff(ex_to<symbol>(x),ex_to<numeric>(m).to_int());
    }
    else
        return pow(-1,2*m)*(factorial(n-m)/factorial(n+m))*pow(1-x*x,m/2)*legendreQ(n,x).diff(ex_to<symbol>(x),ex_to<numeric>(m).to_int());
}

static ex legqm_deriv(const ex& m, const ex& n, const ex & x, unsigned deriv_param)
{
    if (deriv_param == 0)
        throw std::runtime_error("derivative w.r.t. to the index is not supported yet");
    return pow(( ( -1 + pow(( x ),( 2 )) ) ),( -1 )) * ( ( -1 + -1 * n ) * x * legendreQ(n,m,x) + ( 1 + ( -1 * m + n ) ) * legendreQ(1+n,m,x) );
}

static void legqm_print_latex(const ex& m, const ex & n, const ex & x, const print_context & c)
{
    c.s << "\\text{Q}_{"; n.print(c);c.s<<"}^{";m.print(c);c.s<<"}(";x.print(c); c.s << ")";
}

unsigned legendreQ3_SERIAL::serial = function::register_new(function_options("legendreQ", 3).
                                                            eval_func(legqm_eval).
                                                            evalf_func(legqm_evalf).
                                                            derivative_func(legqm_deriv).
                                                            print_func<print_latex>(legqm_print_latex).
                                                            do_not_evalf_params().
                                                            overloaded(2));

//////////
// Hermite polynomials H_n(x)
//////////

static ex hermite_evalf(const ex& n, const ex& x)
{
	if (not is_exactly_a<numeric>(x)
             or not is_exactly_a<numeric>(n))
                return hermiteH(n,x).hold();

    return special_evalf(n,_ex0,x,"hermiteH");
}

static ex hermite_eval(const ex& n, const ex& x)
{
    if (is_exactly_a<numeric>(n)
        and is_exactly_a<numeric>(x)
        and (!ex_to<numeric>(n).info(info_flags::crational)
             or !ex_to<numeric>(x).info(info_flags::crational)))
        return hermiteH(n, x).evalf();

    if (not is_exactly_a<numeric>(n))
            return hermiteH(n, x).hold();
    numeric numn = ex_to<numeric>(n);
    if (not numn.info(info_flags::integer) or numn < 0)
            return hermiteH(n, x).hold();//throw std::runtime_error("hermite_eval: The index n must be a nonnegative integer");

    if (numn.is_zero())
            return _ex1;

    // apply the formula from http://oeis.org/A060821
    // T(n, k) = ((-1)^((n-k)/2))*(2^k)*n!/(k!*((n-k)/2)!) if n-k is even and >=0, else 0.
    // sequentially for all viable k. Effectively there is the recurrence
    // T(n, k) = -(k+2)*(k+1)/(2*(n-k)) * T(n, k+2), with T(n, n) = 2^n
    numeric coeff = _num2_p->pow_intexp(numn);
    ex sum = _ex0;
    int fac = 1;
    epvector vec;
    while (numn >= 0) {
            vec.emplace_back(power(x, numn), coeff);
            coeff /= *_num_4_p;
            coeff *= numn;
            --numn;
            coeff *= numn;
            --numn;
            coeff /= fac++;
            }
    return add(vec);
}

static ex hermite_deriv(const ex& n, const ex & x, unsigned deriv_param)
{
	    if (deriv_param == 0)
                    throw std::runtime_error("derivative w.r.t. to the index is not supported yet");
        return _ex2 * n * hermiteH(n-1, x).hold();
}

static void hermite_print_latex(const ex& n, const ex & x, const print_context & c)
{
    c.s << "\\text{H}_{"; n.print(c);c.s<<"}(";x.print(c); c.s << ")";
}

REGISTER_FUNCTION(hermiteH, eval_func(hermite_eval).
                        evalf_func(hermite_evalf).
                        derivative_func(hermite_deriv).
                        print_func<print_latex>(hermite_print_latex));

//////////
// Gegenbauer (ultraspherical) polynomials C^a_n(x)
//////////

static ex gegenb_evalf(const ex& n, const ex &a, const ex& x)
{
	if (not is_exactly_a<numeric>(x)
             or not is_exactly_a<numeric>(a)
             or not is_exactly_a<numeric>(n))
                return gegenbauerC(n,a,x).hold();

        // see http://dlmf.nist.gov/18.5.E9
    return special_evalf(n,_ex0,x,"gegenbauerC");
}

static ex gegenb_eval(const ex& n, const ex &a, const ex& x)
{
    if (is_exactly_a<numeric>(n)
        and is_exactly_a<numeric>(a)
        and is_exactly_a<numeric>(x)
        and (!ex_to<numeric>(n).info(info_flags::crational)
             or !ex_to<numeric>(a).info(info_flags::crational)
             or !ex_to<numeric>(x).info(info_flags::crational)))
        return gegenbauerC(n,a, x).evalf();

numeric numa = 1;

	if (is_exactly_a<numeric>(x)) {
                const numeric& numx = ex_to<numeric>(x);
                if (is_exactly_a<numeric>(n)
			and is_exactly_a<numeric>(a)
            and !numx.info(info_flags::crational))
                        return gegenb_evalf(n, a, x);
        }

    if (not is_exactly_a<numeric>(n))
            return gegenbauerC(n, a, x).hold();

    const numeric& numn = ex_to<numeric>(n);
    if (not numn.info(info_flags::integer) or numn < 0)
            return gegenbauerC(n, a, x).hold();//throw std::runtime_error("gegenb_eval: The index n must be a nonnegative integer");

    if (numn.is_zero())
            return _ex1;
	if (numn.is_equal(*_num1_p))
		return _ex2 * a * x;

	if (is_exactly_a<numeric>(a)) {
		numa = ex_to<numeric>(a);
		if (numa.is_zero())
			return _ex0; // C_n^0(x) = 0
	}

	if (not is_exactly_a<numeric>(a) or numa < 0) {
		ex p = _ex1;
		ex sum = _ex0;
		ex sign = _ex1;
		ex aa = _ex1;
		long nn = numn.to_long();

		sign = - 1;
		for (long k=0; k<=nn/2; k++) {
			sign *= - 1;
			aa = a;
			p = 1;

			// rising factorial (a)_{n-k}
			for (long i=0; i<nn-k; i++) {
				p *= aa;
				aa = aa + 1;
			}

            p /= factorial(numeric(k));
            p /= factorial(numeric(nn-2*k));
			sum += pow(2*x, nn-2*k) * p * sign;
		}
		return sum;
	}

	// from here on see flint2/fmpq_poly/gegenbauer_c.c
	numeric numer = numa.numer();
    numeric denom = numa.denom();
    numeric t = factorial(numn);
	numeric overall_denom = denom.pow_intexp(numn) * t;

	long nn = numn.to_long();
    numeric p = t / factorial(numeric(nn/2));
	if ((nn%2) != 0u)
		p *= *_num2_p;
	if ((nn&2) != 0u)
		p = -p;

	for (long k=0; k < nn-nn/2; k++) {
		p *= numer;
		numer += denom;
	}

	p *= denom.power(nn/2);
        ex sum = _ex0;
	if ((nn%2) != 0u)
		sum += x*p;
	else
		sum += p;

	for (long k=nn/2-1; k>=0; --k) {
		p *= numer;
		p *= 4*(k+1);
		p *= *_num_1_p;
		p /= denom;
		p /= nn-2*k-1;
		p /= nn-2*k;
		sum += pow(x, nn-2*k) * p;
		numer += denom;
	}

        return sum / overall_denom;
}

static ex gegenb_deriv(const ex& n, const ex & a, const ex & x, unsigned deriv_param)
{
	    if (deriv_param == 0)
                    throw std::runtime_error("derivative w.r.t. to the index is not supported yet");
	    if (deriv_param == 1)
                    throw std::runtime_error("derivative w.r.t. to the second index is not supported yet");

        return _ex2 * a * gegenbauerC(n-1, a+1, x).hold();
}


static void gegenb_print_latex(const ex& n, const ex & m, const ex & x, const print_context & c)
{
    c.s << "\\text{C}_{"; n.print(c);c.s<<"}^{";m.print(c);c.s<<"}(";x.print(c); c.s << ")";
}

REGISTER_FUNCTION(gegenbauerC, eval_func(gegenb_eval).
                              evalf_func(gegenb_evalf).
                              derivative_func(gegenb_deriv).
                              print_func<print_latex>(gegenb_print_latex));


//////////
// Bessel functions J_n(x) (first kind)
//////////
static ex besselj_evalf(const ex& n, const ex& x)
{
    if (not is_exactly_a<numeric>(x)
        or not is_exactly_a<numeric>(n))
        return besselJ(n,x).hold();

    return special_evalf(n,_ex0,x,"besselJ");
}

static ex besselj_eval(const ex& n_, const ex& x)
{
    if (is_exactly_a<numeric>(n_)
        and is_exactly_a<numeric>(x)
        and (!ex_to<numeric>(n_).info(info_flags::crational)
             or !ex_to<numeric>(x).info(info_flags::crational)))
        return besselJ(n_, x).evalf();

    if (not is_exactly_a<numeric>(n_)
        or not n_.info(info_flags::integer))
        return besselJ(n_, x).hold();

    if(n_.info(info_flags::positive))
        return besselJ(n_,x).hold();
    else return -besselJ(-n_,x).hold();

}

static ex besselj_deriv(const ex& n, const ex & x, unsigned deriv_param)
{
    if (deriv_param == 0)
        throw std::runtime_error("derivative w.r.t. to the index is not supported yet");
    //    if(!n.info(info_flags::numeric))
    //        return Diff(legendreQ(n, x).hold(),x);
    return _ex1_2*(besselJ(n-1,x)-besselJ(n+1,x));
}

static void besselj_print_latex(const ex& n, const ex & x, const print_context & c)
{
    c.s << "\\text{J}_{"; n.print(c);c.s<<"}(";x.print(c); c.s << ")";
}


REGISTER_FUNCTION(besselJ, eval_func(besselj_eval).
                           evalf_func(besselj_evalf).
                           derivative_func(besselj_deriv).
                           print_func<print_latex>(besselj_print_latex));

//////////
// Bessel functions Y_n(x) (second kind)
//////////
static ex bessely_evalf(const ex& n, const ex& x)
{
    if (not is_exactly_a<numeric>(x)
        or not is_exactly_a<numeric>(n))
        return besselY(n,x).hold();

    return special_evalf(n,_ex0,x,"besselY");
}

static ex bessely_eval(const ex& n_, const ex& x)
{
    if (is_exactly_a<numeric>(n_)
        and is_exactly_a<numeric>(x)
        and (!ex_to<numeric>(n_).info(info_flags::crational)
             or !ex_to<numeric>(x).info(info_flags::crational)))
        return besselY(n_, x).evalf();

    if (not is_exactly_a<numeric>(n_)
        or not n_.info(info_flags::integer))
        return besselY(n_, x).hold();

    if(n_.info(info_flags::positive))
        return besselY(n_,x).hold();
    else return -besselY(-n_,x).hold();

}

static ex bessely_deriv(const ex& n, const ex & x, unsigned deriv_param)
{
    if (deriv_param == 0)
        throw std::runtime_error("derivative w.r.t. to the index is not supported yet");
    //    if(!n.info(info_flags::numeric))
    //        return Diff(legendreQ(n, x).hold(),x);
    return _ex1_2*(besselY(n-1,x)-besselY(n+1,x));
}

static void bessely_print_latex(const ex& n, const ex & x, const print_context & c)
{
    c.s << "\\text{Y}_{"; n.print(c);c.s<<"}(";x.print(c); c.s << ")";
}


REGISTER_FUNCTION(besselY, eval_func(bessely_eval).
                           evalf_func(bessely_evalf).
                           derivative_func(bessely_deriv).
                           print_func<print_latex>(bessely_print_latex));


//////////
// modified Bessel functions I_n(x) (first kind)
//////////
static ex besseli_evalf(const ex& n, const ex& x)
{
    if (not is_exactly_a<numeric>(x)
        or not is_exactly_a<numeric>(n))
        return besselI(n,x).hold();

    return special_evalf(n,_ex0,x,"besselI");
}

static ex besseli_eval(const ex& n_, const ex& x)
{
    if (is_exactly_a<numeric>(n_)
        and is_exactly_a<numeric>(x)
        and (!ex_to<numeric>(n_).info(info_flags::crational)
             or !ex_to<numeric>(x).info(info_flags::crational)))
        return besselI(n_, x).evalf();

    if (not is_exactly_a<numeric>(n_)
        or not n_.info(info_flags::integer))
        return besselI(n_, x).hold();

    if(n_.info(info_flags::positive))
        return besselI(n_,x).hold();
    else return besselI(-n_,x).hold();

}

static ex besseli_deriv(const ex& n, const ex & x, unsigned deriv_param)
{
    if (deriv_param == 0)
        throw std::runtime_error("derivative w.r.t. to the index is not supported yet");
    //    if(!n.info(info_flags::numeric))
    //        return Diff(legendreQ(n, x).hold(),x);
    return _ex1_2*(besselI(n-1,x)+besselI(n+1,x));
}

static void besseli_print_latex(const ex& n, const ex & x, const print_context & c)
{
    c.s << "\\text{I}_{"; n.print(c);c.s<<"}(";x.print(c); c.s << ")";
}


REGISTER_FUNCTION(besselI, eval_func(besseli_eval).
                           evalf_func(besseli_evalf).
                           derivative_func(besseli_deriv).
                           print_func<print_latex>(besseli_print_latex));

//////////
// modified Bessel functions K_n(x) (second kind)
//////////
static ex besselk_evalf(const ex& n, const ex& x)
{
    if (not is_exactly_a<numeric>(x)
        or not is_exactly_a<numeric>(n))
        return besselK(n,x).hold();

    return special_evalf(n,_ex0,x,"besselK");
}

static ex besselk_eval(const ex& n_, const ex& x)
{
    if (is_exactly_a<numeric>(n_)
        and is_exactly_a<numeric>(x)
        and (!ex_to<numeric>(n_).info(info_flags::crational)
             or !ex_to<numeric>(x).info(info_flags::crational)))
        return besselK(n_, x).evalf();

    if (not is_exactly_a<numeric>(n_)
        or not n_.info(info_flags::integer))
        return besselK(n_, x).hold();

    if(n_.info(info_flags::positive))
        return besselK(n_,x).hold();
    else return besselK(-n_,x).hold();

}

static ex besselk_deriv(const ex& n, const ex & x, unsigned deriv_param)
{
    if (deriv_param == 0)
        throw std::runtime_error("derivative w.r.t. to the index is not supported yet");
    //    if(!n.info(info_flags::numeric))
    //        return Diff(legendreQ(n, x).hold(),x);
    return _ex_1_2*(besselK(n-1,x)+besselK(n+1,x));
}

static void besselk_print_latex(const ex& n, const ex & x, const print_context & c)
{
    c.s << "\\text{K}_{"; n.print(c);c.s<<"}(";x.print(c); c.s << ")";
}


REGISTER_FUNCTION(besselK, eval_func(besselk_eval).
                           evalf_func(besselk_evalf).
                           derivative_func(besselk_deriv).
                           print_func<print_latex>(besselk_print_latex));




//////////
//  Dummy Jacobi Elliptic Functions
//////////
REGISTER_FUNCTION(JacobiSN, dummy())
REGISTER_FUNCTION(JacobiCN, dummy())
REGISTER_FUNCTION(JacobiDN, dummy())
REGISTER_FUNCTION(JacobiNS, dummy())
REGISTER_FUNCTION(JacobiNC, dummy())
REGISTER_FUNCTION(JacobiND, dummy())
REGISTER_FUNCTION(JacobiSC, dummy())
REGISTER_FUNCTION(JacobiSD, dummy())
REGISTER_FUNCTION(JacobiCS, dummy())
REGISTER_FUNCTION(JacobiDS, dummy())
REGISTER_FUNCTION(sn, dummy())
REGISTER_FUNCTION(cn, dummy())
REGISTER_FUNCTION(dn, dummy())

} // namespace ginacsym
