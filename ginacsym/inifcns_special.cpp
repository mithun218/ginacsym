/** @file inifcns_special.cpp
 *
 *  Implementation of special functions.
 **/
/*
 *  Copyright (C) 2024 Mithun Bairagi <bairagirasulpur@gmail.com>
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

#include "ginacwrapper.h"
#include "inifcns.h"
#include "ex.h"
#include "constant.h"
#include "infinity.h"
#include "numeric.h"
#include "add.h"
#include "mul.h"
#include "power.h"
#include "operators.h"
#include "symbol.h"
#include "utility.h"
#include "utils.h"

#include "flint/fmpz_poly.h"
#include "flint/fmpq.h"
#include "flint/acb.h"
#include "flint/acb_hypgeom.h"

namespace ginacsym {
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
} // namespace ginacsym
