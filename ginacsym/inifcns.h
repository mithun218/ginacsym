/** @file inifcns.h
 *
 *  Interface to ginacsym's initially known functions. */

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

#ifndef GINAC_INIFCNS_H
#define GINAC_INIFCNS_H

#include "numeric.h"
#include "function.h"
#include "ex.h"

namespace ginacsym {

/** Complex conjugate. */
DECLARE_FUNCTION_1P(conjugate_function)

/** Real part. */
DECLARE_FUNCTION_1P(real_part_function)

/** Imaginary part. */
DECLARE_FUNCTION_1P(imag_part_function)
	
/** Absolute value. */
DECLARE_FUNCTION_1P(abs)
	
/** Step function. */
DECLARE_FUNCTION_1P(step)

/** Heaviside function. */
DECLARE_FUNCTION_1P(heaviside)

/** Formal piecewise function */
DECLARE_FUNCTION_1P(cases)
	
/** Complex sign. */
DECLARE_FUNCTION_1P(csgn)

/** Eta function: log(a*b) == log(a) + log(b) + eta(a, b). */
DECLARE_FUNCTION_2P(eta)


/** Exponential function. */
DECLARE_FUNCTION_1P(exp)

/** Natural logarithm. */
DECLARE_FUNCTION_1P(log)

/** General logarithm. */
DECLARE_FUNCTION_2P(logb)


/** Sine. */
DECLARE_FUNCTION_1P(sin)

/** Cosine. */
DECLARE_FUNCTION_1P(cos)

/** Tangent. */
DECLARE_FUNCTION_1P(tan)

/** Cotangent. */
DECLARE_FUNCTION_1P(cot)

/** Secant. */
DECLARE_FUNCTION_1P(sec)

/** Cosecant. */
DECLARE_FUNCTION_1P(csc)

/** Inverse sine (arc sine). */
DECLARE_FUNCTION_1P(asin)

/** Inverse cosine (arc cosine). */
DECLARE_FUNCTION_1P(acos)

/** Inverse tangent (arc tangent). */
DECLARE_FUNCTION_1P(atan)

/** Inverse tangent with two arguments. */
DECLARE_FUNCTION_2P(atan2)

/** Inverse cotangent (arc cotangent). */
DECLARE_FUNCTION_1P(acot)

/** Inverse secant (arc secant). */
DECLARE_FUNCTION_1P(asec)

/** Inverse cosecant (arc cosecant). */
DECLARE_FUNCTION_1P(acsc)


/** Hyperbolic Sine. */
DECLARE_FUNCTION_1P(sinh)

/** Hyperbolic Cosine. */
DECLARE_FUNCTION_1P(cosh)

/** Hyperbolic Tangent. */
DECLARE_FUNCTION_1P(tanh)

/** Hyperbolic Cotangent. */
DECLARE_FUNCTION_1P(coth)

/** Hyperbolic Secant. */
DECLARE_FUNCTION_1P(sech)

/** Hyperbolic Cosecant. */
DECLARE_FUNCTION_1P(csch)

/** Inverse hyperbolic Sine (area hyperbolic sine). */
DECLARE_FUNCTION_1P(asinh)

/** Inverse hyperbolic Cosine (area hyperbolic cosine). */
DECLARE_FUNCTION_1P(acosh)

/** Inverse hyperbolic Tangent (area hyperbolic tangent). */
DECLARE_FUNCTION_1P(atanh)

/** Inverse hyperbolic Cotangent (area hyperbolic cotangent). */
DECLARE_FUNCTION_1P(acoth)

/** Inverse hyperbolic Cosecant (area hyperbolic cosecant). */
DECLARE_FUNCTION_1P(acsch)

/** Inverse hyperbolic Secant (area hyperbolic secant). */
DECLARE_FUNCTION_1P(asech)


/** Dilogarithm. */
DECLARE_FUNCTION_1P(Li2)

/** Trilogarithm. */
DECLARE_FUNCTION_1P(Li3)

/** Derivatives of Riemann's Zeta-function. */
DECLARE_FUNCTION_2P(zetaderiv)

// overloading at work: we cannot use the macros here
/** Multiple zeta value including Riemann's zeta-function. */
class zeta1_SERIAL { public: static unsigned serial; };
template<typename T1>
inline function zeta(const T1& p1) {
	return function(zeta1_SERIAL::serial, ex(p1));
}
/** Alternating Euler sum or colored MZV. */
class zeta2_SERIAL { public: static unsigned serial; };
template<typename T1, typename T2>
inline function zeta(const T1& p1, const T2& p2) {
	return function(zeta2_SERIAL::serial, ex(p1), ex(p2));
}
class zeta_SERIAL;
template<> inline bool is_the_function<zeta_SERIAL>(const ex& x)
{
	return is_the_function<zeta1_SERIAL>(x) || is_the_function<zeta2_SERIAL>(x);
}

// overloading at work: we cannot use the macros here
/** Generalized multiple polylogarithm. */
class G2_SERIAL { public: static unsigned serial; };
template<typename T1, typename T2>
inline function G(const T1& x, const T2& y) {
	return function(G2_SERIAL::serial, ex(x), ex(y));
}
/** Generalized multiple polylogarithm with explicit imaginary parts. */
class G3_SERIAL { public: static unsigned serial; };
template<typename T1, typename T2, typename T3>
inline function G(const T1& x, const T2& s, const T3& y) {
	return function(G3_SERIAL::serial, ex(x), ex(s), ex(y));
}
class G_SERIAL;
template<> inline bool is_the_function<G_SERIAL>(const ex& x)
{
	return is_the_function<G2_SERIAL>(x) || is_the_function<G3_SERIAL>(x);
}

/** Polylogarithm and multiple polylogarithm. */
DECLARE_FUNCTION_2P(Li)

/** Nielsen's generalized polylogarithm. */
DECLARE_FUNCTION_3P(S)

/** Harmonic polylogarithm. */
DECLARE_FUNCTION_2P(H)

/** Gamma-function. */
DECLARE_FUNCTION_1P(lgamma)
DECLARE_FUNCTION_1P(tgamma)

/** Beta-function. */
DECLARE_FUNCTION_2P(beta)

/**integral functions**/
DECLARE_FUNCTION_1P(sinIntegral)
DECLARE_FUNCTION_1P(cosIntegral)
DECLARE_FUNCTION_1P(sinhIntegral)
DECLARE_FUNCTION_1P(coshIntegral)
DECLARE_FUNCTION_1P(logIntegral)
DECLARE_FUNCTION_1P(expIntegralEi)
DECLARE_FUNCTION_2P(expIntegralE)

// overloading at work: we cannot use the macros here
/** Psi-function (aka digamma-function). */
class psi1_SERIAL { public: static unsigned serial; };
template<typename T1>
inline function psi(const T1 & p1) {
	return function(psi1_SERIAL::serial, ex(p1));
}
/** Derivatives of Psi-function (aka polygamma-functions). */
class psi2_SERIAL { public: static unsigned serial; };
template<typename T1, typename T2>
inline function psi(const T1 & p1, const T2 & p2) {
	return function(psi2_SERIAL::serial, ex(p1), ex(p2));
}
class psi_SERIAL;
template<> inline bool is_the_function<psi_SERIAL>(const ex & x)
{
	return is_the_function<psi1_SERIAL>(x) || is_the_function<psi2_SERIAL>(x);
}
	
/** Complete elliptic integral of the first kind. */
DECLARE_FUNCTION_1P(EllipticK)

/** Complete elliptic integral of the second kind. */
DECLARE_FUNCTION_1P(EllipticE)

// overloading at work: we cannot use the macros here
/** Iterated integral. */
class iterated_integral2_SERIAL { public: static unsigned serial; };
template<typename T1, typename T2>
inline function iterated_integral(const T1& kernel_lst, const T2& lambda) {
	return function(iterated_integral2_SERIAL::serial, ex(kernel_lst), ex(lambda));
}
/** Iterated integral with explicit truncation. */
class iterated_integral3_SERIAL { public: static unsigned serial; };
template<typename T1, typename T2, typename T3>
inline function iterated_integral(const T1& kernel_lst, const T2& lambda, const T3& N_trunc) {
	return function(iterated_integral3_SERIAL::serial, ex(kernel_lst), ex(lambda), ex(N_trunc));
}
class iterated_integral_SERIAL;
template<> inline bool is_the_function<iterated_integral_SERIAL>(const ex& x)
{
	return is_the_function<iterated_integral2_SERIAL>(x) || is_the_function<iterated_integral3_SERIAL>(x);
}


/** Factorial function. */
DECLARE_FUNCTION_1P(factorial)

/** Binomial function. */
DECLARE_FUNCTION_2P(binomial)

/** Order term function (for truncated power series). */
DECLARE_FUNCTION_1P(Order)

ex lsolve(const ex &eqns, const ex &symbols, unsigned options = solve_algo::automatic);

/** Find a real root of real-valued function f(x) numerically within a given
 *  interval. The function must change sign across interval. Uses Newton-
 *  Raphson method combined with bisection in order to guarantee convergence.
 *
 *  @param f  Function f(x)
 *  @param x  Symbol f(x)
 *  @param x1  lower interval limit
 *  @param x2  upper interval limit
 *  @exception runtime_error (if interval is invalid). */
const numeric fsolve(const ex& f, const symbol& x, const numeric& x1, const numeric& x2);

/** Check whether a function is the Order (O(n)) function. */
inline bool is_order_function(const ex & e)
{
	return is_ex_the_function(e, Order);
}

/** Converts a given list containing parameters for H in Remiddi/Vermaseren notation into
 *  the corresponding ginacsym functions.
 */
ex convert_H_to_Li(const ex& parameterlst, const ex& arg);


/** Chebyshev T polynomial. */
DECLARE_FUNCTION_2P(chebyshevT)

/** Chebyshev U polynomial. */
DECLARE_FUNCTION_2P(chebyshevU)



// overloading at work: we cannot use the macros here
/** Legendre P polynomial. */
class legendreP2_SERIAL { public: static unsigned serial; };
template<typename T1, typename T2>
inline function legendreP(const T1& n, const T2& x) {
    return function(legendreP2_SERIAL::serial, ex(n), ex(x));
}
/** associated Legendre P polynomial. */
class legendreP3_SERIAL { public: static unsigned serial; };
template<typename T1, typename T2, typename T3>
inline function  legendreP(const T1& m, const T2& n, const T3& x) {
    return function( legendreP3_SERIAL::serial, ex(m), ex(n), ex(x));
}
class legendreP_SERIAL;
template<> inline bool is_the_function<legendreP_SERIAL>(const ex& x)
{
    return is_the_function<legendreP2_SERIAL>(x) || is_the_function<legendreP3_SERIAL>(x);
}

// overloading at work: we cannot use the macros here
/** Legendre Q function. */
class legendreQ2_SERIAL { public: static unsigned serial; };
template<typename T1, typename T2>
inline function legendreQ(const T1& n, const T2& x) {
    return function(legendreQ2_SERIAL::serial, ex(n), ex(x));
}
/** associated Legendre Q function. */
class legendreQ3_SERIAL { public: static unsigned serial; };
template<typename T1, typename T2, typename T3>
inline function  legendreQ(const T1& m, const T2& n, const T3& x) {
    return function( legendreQ3_SERIAL::serial, ex(m), ex(n), ex(x));
}
class legendreQ_SERIAL;
template<> inline bool is_the_function<legendreQ_SERIAL>(const ex& x)
{
    return is_the_function<legendreQ2_SERIAL>(x) || is_the_function<legendreQ3_SERIAL>(x);
}


/** Hermite polynomial. */
DECLARE_FUNCTION_2P(hermiteH)

/** Gegenbauer (ultraspherical) polynomial. */
DECLARE_FUNCTION_3P(gegenbauerC)

/** Bessel J function (first kind). */
DECLARE_FUNCTION_2P(besselJ)

/** Bessel Y function (second kind). */
DECLARE_FUNCTION_2P(besselY)

/** Modified Bessel functions (first kind). */
DECLARE_FUNCTION_2P(besselI)

/** Modified Bessel functions (second kind). */
DECLARE_FUNCTION_2P(besselK)


/** Dummy Jacobi Elliptic Functions **/
DECLARE_FUNCTION_2P(JacobiSN)
DECLARE_FUNCTION_2P(JacobiCN)
DECLARE_FUNCTION_2P(JacobiDN)
DECLARE_FUNCTION_2P(JacobiNS)
DECLARE_FUNCTION_2P(JacobiNC)
DECLARE_FUNCTION_2P(JacobiND)
DECLARE_FUNCTION_2P(JacobiSC)
DECLARE_FUNCTION_2P(JacobiSD)
DECLARE_FUNCTION_2P(JacobiCS)
DECLARE_FUNCTION_2P(JacobiDS)
DECLARE_FUNCTION_1P(sn)
DECLARE_FUNCTION_1P(cn)
DECLARE_FUNCTION_1P(dn)

/** Helping functions for Diff,Integrate
 *  to parse them from string
 *  **/
DECLARE_FUNCTION_3P(Diff_helper)
DECLARE_FUNCTION_2P(Integrate_helper)


} // namespace ginacsym

#endif // ndef GINAC_INIFCNS_H
