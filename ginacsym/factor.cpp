/** @file factor.cpp
 *
 *  Polynomial factorization (implementation).
 *
 *  The interface function factor() at the end of this file is defined in the
 *  ginacsym namespace. All other utility functions and classes are defined in an
 *  additional anonymous namespace.
 *
 *  Factorization starts by doing a square free factorization and making the
 *  coefficients integer. Then, depending on the number of free variables it
 *  proceeds either in dedicated univariate or multivariate factorization code.
 *
 *  Univariate factorization does a modular factorization via Berlekamp's
 *  algorithm and distinct degree factorization. Hensel lifting is used at the
 *  end.
 *  
 *  Multivariate factorization uses the univariate factorization (applying a
 *  evaluation homomorphism first) and Hensel lifting raises the answer to the
 *  multivariate domain. The Hensel lifting code is completely distinct from the
 *  code used by the univariate factorization.
 *
 *  Algorithms used can be found in
 *    [Wan] An Improved Multivariate Polynomial Factoring Algorithm,
 *          P.S.Wang,
 *          Mathematics of Computation, Vol. 32, No. 144 (1978) 1215--1231.
 *    [GCL] Algorithms for Computer Algebra,
 *          K.O.Geddes, S.R.Czapor, G.Labahn,
 *          Springer Verlag, 1992.
 *    [Mig] Some Useful Bounds,
 *          M.Mignotte, 
 *          In "Computer Algebra, Symbolic and Algebraic Computation" (B.Buchberger et al., eds.),
 *          pp. 259-263, Springer-Verlag, New York, 1982.
 */

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

//#define DEBUGFACTOR

#include "factor.h"

#include "ex.h"
#include "operators.h"
#include "power.h"
#include "mul.h"
#include "normal.h"
#include "add.h"
#include "ginacwrapper.h"
#include "utility.h"

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_factor.h>
#include <flint/fmpz_mpoly.h>
#include <flint/fmpz_mpoly_factor.h>


#include <vector>
#ifdef DEBUGFACTOR
#include <ostream>
#endif
using namespace std;

#include <cln/cln.h>
using namespace cln;

namespace ginacsym {

// anonymous namespace to hide all utility functions
namespace {

#ifdef DEBUGFACTOR
#define DCOUT(str) cout << #str << endl
#define DCOUTVAR(var) cout << #var << ": " << var << endl
#define DCOUT2(str,var) cout << #str << ": " << var << endl
ostream& operator<<(ostream& o, const vector<int>& v)
{
	auto i = v.begin(), end = v.end();
	while ( i != end ) {
		o << *i << " ";
		++i;
	}
	return o;
}
static ostream& operator<<(ostream& o, const vector<cl_I>& v)
{
	auto i = v.begin(), end = v.end();
	while ( i != end ) {
		o << *i << "[" << i-v.begin() << "]" << " ";
		++i;
	}
	return o;
}
static ostream& operator<<(ostream& o, const vector<cl_MI>& v)
{
	auto i = v.begin(), end = v.end();
	while ( i != end ) {
		o << *i << "[" << i-v.begin() << "]" << " ";
		++i;
	}
	return o;
}
ostream& operator<<(ostream& o, const vector<numeric>& v)
{
	for ( size_t i=0; i<v.size(); ++i ) {
		o << v[i] << " ";
	}
	return o;
}
ostream& operator<<(ostream& o, const vector<vector<cl_MI>>& v)
{
	auto i = v.begin(), end = v.end();
	while ( i != end ) {
		o << i-v.begin() << ": " << *i << endl;
		++i;
	}
	return o;
}
#else
#define DCOUT(str)
#define DCOUTVAR(var)
#define DCOUT2(str,var)
#endif // def DEBUGFACTOR



/** Map used by factor() when factor_options::all is given to access all
 *  subexpressions and to call factor() on them.
 */
struct apply_factor_map : public map_function {
	unsigned options;
	apply_factor_map(unsigned options_) : options(options_) { }
    ex expr_visitor(const ex& e) override
	{
		if ( e.info(info_flags::polynomial) ) {
			return factor(e, options);
		}
		if ( is_a<add>(e) ) {
			ex s1, s2;
			for ( size_t i=0; i<e.nops(); ++i ) {
				if ( e.op(i).info(info_flags::polynomial) ) {
					s1 += e.op(i);
				} else {
					s2 += e.op(i);
				}
			}
			return factor(s1, options) + s2.map(*this);
		}
		return e.map(*this);
	}
};

/** Iterate through explicit factors of e, call yield(f, k) for
 *  each factor of the form f^k.
 *
 *  Note that this function doesn't factor e itself, it only
 *  iterates through the factors already explicitly present.
 */
template <typename F> void
factor_iter(const ex &e, F yield)
{
	if (is_a<mul>(e)) {
		for (const auto &f : e) {
			if (is_a<power>(f)) {
				yield(f.op(0), f.op(1));
			} else {
				yield(f, ex(1));
			}
		}
	} else {
		if (is_a<power>(e)) {
			yield(e.op(0), e.op(1));
		} else {
			yield(e, ex(1));
		}
	}
}

/** This function factorizes a polynomial. It checks the arguments,
 *  tries a square free factorization, and then calls factor_sqrfree
 *  to do the hard work.
 *
 *  This function expands its argument, so for polynomials with
 *  explicit factors it's better to call it on each one separately
 *  (or use factor() which does just that).
 */
static ex factor1(const ex& poly, unsigned options)
{    
	// check arguments
	if ( !poly.info(info_flags::polynomial) ) {
		if ( options & factor_options::all ) {
			options &= ~factor_options::all;
			apply_factor_map factor_map(options);
            return factor_map.expr_visitor(poly);
		}
		return poly;
	}

	// determine all symbols in poly
	find_symbols_map findsymbols;
    findsymbols.expr_visitor(poly);
	if ( findsymbols.syms.size() == 0 ) {
		return poly;
	}
	lst syms;
    std::vector<string> symsstr;
    string str;
    size_t symstrmaxsize=0;
	for (auto & i : findsymbols.syms ) {
		syms.append(i);
        str=to_string(i);
        symsstr.push_back(str);
        if(symstrmaxsize<str.size()) symstrmaxsize=str.size();
	}

    ex poly_numer=numer(poly),poly_denom=denom(poly);

    fmpz_mpoly_t f;
    fmpz_mpoly_ctx_t mctx;
    fmpz_mpoly_factor_t fac;
//    slong i;
//    int num_threads = 1;
//    int timing = 0;
//    int suppress = 0;
    const char * vars[symsstr.size()];
    //const char * vars[] = { "x", "y","b"};
    char charr[symsstr.size()+1][symstrmaxsize+1];
    size_t symsstrpos=0;
    for (auto i = symsstr.begin(); i != symsstr.end();i++) {
        for(unsigned j=0;j<(*i).size()+1;j++){
            charr[symsstrpos][j]=(*i)[j];
        }
        vars[symsstrpos]=charr[symsstrpos];
        symsstrpos=symsstrpos+1;
    }

    fmpz_mpoly_ctx_init(mctx, symsstr.size(), ORD_LEX);
    fmpz_mpoly_init(f, mctx);
    fmpz_mpoly_factor_init(fac, mctx);
    //flint_set_num_threads(3);
    int rint=fmpz_mpoly_set_str_pretty(f,to_string(poly_numer).c_str(), vars, mctx);
    if(rint)
        return poly;
    rint=fmpz_mpoly_factor(fac, f, mctx);
    if(!rint)
        return poly;
    //fmpz_mpoly_print_pretty(f, vars, mctx);
    //fmpz_mpoly_factor_print_pretty(fac,vars,mctx);
    const int factorlength=fmpz_mpoly_factor_length(fac,mctx);
    fmpz_t factorconstant;
    fmpz_init(factorconstant);
    fmpz_mpoly_factor_get_constant_fmpz(factorconstant,fac,mctx);
    string factorstr=fmpz_get_str(nullptr,10,factorconstant);
    for(int i=0;i<factorlength;i++){
        fmpz_mpoly_factor_get_base(f,fac,i,mctx);
        factorstr=factorstr+"*("+fmpz_mpoly_get_str_pretty(f,vars,mctx)+")";
        factorstr=factorstr+"^"+to_string(fmpz_mpoly_factor_get_exp_si(fac,i,mctx));
    }

    fmpz_mpoly_factor_clear(fac, mctx);
    fmpz_mpoly_clear(f, mctx);
    fmpz_mpoly_ctx_clear(mctx);
    flint_cleanup_master();
    return generator.exGeneratorFromString(factorstr)/poly_denom;



//	// make poly square free
//	ex sfpoly = sqrfree(poly.expand(), syms);

//	// factorize the square free components
//	ex res = 1;
//	factor_iter(sfpoly,
//		[&](const ex &f, const ex &k) {
//			if ( is_a<add>(f) ) {
//				res *= pow(factor_sqrfree(f), k);
//			} else {
//				// simple case: (monomial)^exponent
//				res *= pow(f, k);
//			}
//		});
//	return res;
}

} // anonymous namespace

/** Interface function to the outside world. It uses factor1()
 *  on each of the explicitly present factors of poly.
 */
ex factor(const ex& poly, unsigned options)
{
	ex result = 1;
	factor_iter(poly,
		[&](const ex &f1, const ex &k1) {
			factor_iter(factor1(f1, options),
				[&](const ex &f2, const ex &k2) {
					result *= pow(f2, k1*k2);
				});
		});
	return result;
}

ex expandflint(const ex& e, unsigned options)
{
    exmap ma;
    ex basicexpoly=e.to_polynomial(ma);
    for (auto i:ma)
        generator.symRegister(i.first);

    // determine all symbols in poly
    find_symbols_map findsymbols;
    findsymbols.expr_visitor(basicexpoly);
    if ( findsymbols.syms.size() == 0 ) {
        return basicexpoly;
    }
    lst syms;
    std::vector<std::string> symsstr;
    std::string str;
    size_t symstrmaxsize=0;
    for (auto & i : findsymbols.syms ) {
        syms.append(i);
        str=to_string(i);
        symsstr.push_back(str);
        if(symstrmaxsize<str.size()) symstrmaxsize=str.size();
    }

    fmpz_mpoly_t f;
    fmpz_mpoly_ctx_t mctx;
    //    slong i;
    //    int num_threads = 1;
    //    int timing = 0;
    //    int suppress = 0;
    const char * vars[symsstr.size()];
    //const char * vars[] = { "x", "y","b"};
    char charr[symsstr.size()+1][symstrmaxsize+1];
    size_t symsstrpos=0;
    for (auto i = symsstr.begin(); i != symsstr.end();i++) {
        for(unsigned j=0;j<(*i).size()+1;j++){
            charr[symsstrpos][j]=(*i)[j];
        }
        vars[symsstrpos]=charr[symsstrpos];
        symsstrpos=symsstrpos+1;
    }

    fmpz_mpoly_ctx_init(mctx, symsstr.size(), ORD_LEX);
    fmpz_mpoly_init(f, mctx);
    //flint_set_num_threads(3);
    fmpz_mpoly_set_str_pretty(f,to_string(basicexpoly).c_str(), vars, mctx);
    const std::string basicexpolyexpastr=  fmpz_mpoly_get_str_pretty(f,vars, mctx);
    ex basicexpolyexpaex=  generator.exGeneratorFromString(basicexpolyexpastr);
    if(!ma.empty())
        basicexpolyexpaex=basicexpolyexpaex.subs(ma);
    return basicexpolyexpaex.expand(options);
}

} // namespace ginacsym
