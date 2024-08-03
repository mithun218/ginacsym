
/** @file utility.cpp
 *
 *  Implementation of some usefull utilities used in other files. **/

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

#include <sstream>
#include<cln/exception.h>
#include "utility.h"
#include "factor.h"
#include "fail.h"
#include "functions.h"
#include "inert.h"
#include "normal.h"
#include "outform.h"
#include "simplify.h"
#include "add.h"
#include "mul.h"
#include "power.h"


namespace ginacsym{

    const numeric _numeric1(1),_numeric2(2),_numeric3(3),_numeric4(4);
    symbol_finderc symbol_finder;

    std::chrono::time_point<std::chrono::system_clock> beginTime;

    //string CurrentPath, filename = "outputResults.txt";


    exmapexvec var_depend;

    std::vector<lst> solutionClt; lst constraints = {};

    slong _digits=17*3.33;

    bool has_only_digits(const std::string s)
    {
        return s.find_first_not_of("0123456789") == std::string::npos;
    }
    /////////////////////////////////////////////////////////////

    std::vector<std::string> split (const std::string &s, char delim)
    {
        std::vector<std::string> result;
        std::stringstream ss (s);
        std::string item;

        while (getline (ss, item, delim)) {
            result.push_back (item);
        }

        return result;
    }
    /////////////////////////////////////////////////////////////

    /** converting number containing decimal point to rational, 1.252 = 1252/1000 **/
    ex DoubleToRational(ex _a)
    {
        std::ostringstream s;
        s<<_a;
        std::string tem1 = s.str();

        if((tem1.find('E')) != std::string::npos)
        {
            std::vector<std::string> ve = split (tem1, 'E');
            size_t zeronum=stoi(ve[1]);
            if(ve[0].find('.') != std::string::npos)
            {
                std::vector<std::string> vd = split (ve[0], '.');
                const size_t decipos = vd[1].length();
                zeronum=zeronum-decipos;
                ve[0]=replacestring(ve[0],".","");
            }

            std::string strCreate;
            if(zeronum>0)
                strCreate = ve[0]+"*10^"+to_string(zeronum);
            else
                strCreate = ve[0]+"*10^(-"+to_string(zeronum)+")";

            return symbol(strCreate);
        }

        int j = 0; // position of decimal point
        bool cond = true;
        auto itr = tem1.rbegin();
        do
        {
            if(*itr == '.')
            {
                cond = false;
            }
            else
            {
                j = j + 1;
                itr++;
            }
        }while(cond && itr != tem1.rend());

        if(!cond)
        {
            tem1.erase(find(tem1.begin(),tem1.end(), '.'));
            return symbol(tem1)/pow(_ex1*10,j);
        }
        return _a;
    }


    /** converting number containing decimal point to rational, 1.252 = 1252/1000 **/
    ex dorat::expr_visitor(const ex& _e)
    {
        if (is_a<numeric>(_e) &&
            !(_e).info(info_flags::rational) && !(_e).info(info_flags::crational))
        {
            israt = false;

            if((_e.info(info_flags::positive) && _e < Gtolerance) ||
                (_e.info(info_flags::negative) && -_e < Gtolerance))
                return _ex0;

            if((_e).info(info_flags::real))
                return DoubleToRational(_e);
            else
            {
                return DoubleToRational(real_part(_e))
                       + I*DoubleToRational(imag_part(_e));
            }
        }

        return _e.map(*this);
    }


    /** replacing power having "add" base with generated symbols **/ // used in Factor
    ex powBaseSubs::expr_visitor(const ex& _e)
    {
        if((is_a<power>(_e)&&is_a<numeric>(_e.op(1))&&(is_a<add>(_e.op(0))))
            ||(isNu &&is_a<power>(_e)&&_e.op(1).info(info_flags::real) && _e.op(1) < _ex0 && is_a<add>(_e.op(0))))
        {
            if((!exprToSymMap.empty() && exprToSymMap.find(_e.op(0))==exprToSymMap.end())
                ||exprToSymMap.empty())
            {
                j=j+1;

                str = "powSubs_" + to_string(j);
                expr = generator.symGenerator(str);
                exprToSymMap[_e.op(0)]=expr;
            }

            if(!exprToSymMap.empty() && exprToSymMap.find(_e.op(0))!=exprToSymMap.end())
                return pow(exprToSymMap[_e.op(0)],_e.op(1));
        }

        else if(!isNu&&is_a<add>(_e))
            addNum=(addNum+nops(_e))-1;

        return _e.map(*this);
    };


    /** Polynomial factorization with number containing decimal point and higher degree with "add" base.
    prefactor terms are skipping. **/
    ex Factor(const ex& expr)
    {
        ex temex;

        if(expr.has(I)) // avoiding I in function. Inbuilt factor does not work when I is present.
        {
            replaceI replaceId;
            temex = replaceId.expr_visitor(expr);
        }
        else
            temex = expr;

        if( conjuFreee.expr_visitor(temex) == temex && conjuFreee.expr_visitor(conjugate(temex)) == temex && !is_a<numeric>(temex) ) // avoiding factor containing conjugate and numerics
        {
            powBaseSubs powSubs(0); //replacing power having "add" base with generated symbols
            fracPowBasSubsFactor fracPow; // replacing base having fractional power.
            fracPow.set();
            temex=fracPow.expr_visitor(temex);

            temex = powSubs.expr_visitor(temex);// avoiding higher degree with "add" base

            //dorat dorat; // avoiding double form
            // dorat.set();

            try
            {
                if(powSubs.addNum<=addNumFrFactr)
                {
                    //cout<<"temexpr_6 "<< temex<<endl;
                    temex = factor((temex));
                    //temex = collect_common_factors((temex));
                    //cout<<"temexpr_7"<< temex<<endl;
                }
                else
                    temex = collect_common_factors((temex));
            }
            catch (cln::runtime_exception){} // ginacsym has a bug in factor(). Sometime this error occur.
            catch (std::invalid_argument){}


            temex = genSymbSubs(temex,powSubs.exprToSymMap);
            if(!fracPow.baseClt.empty())
            {
                temex = genSymbSubs(temex,fracPow.baseClt);
            }

            if(temex.has(externSymbols.symb_))
                temex = temex.subs({externSymbols.symb_ == I});

            //if(dorat.israt)
            return temex;
            // else
            //   return evalf(temex);


        }
        else
            return expr;
    }

    /** calculating gcd of list of expressions (also support rational number: such as {8/7,b/7*b} ) **/
    ex Gcd(lst exp)
    {
        if (nops(exp)==1) {
            return exp[0];
        }
        bool err = false; //isr = true;
        ex tem;
        //dorat dorat; // avoiding double form
        //dorat.set();
        //exp[0] = dorat(exp[0]);
        //if(!dorat.israt)
        //    isr = false;
        while(nops(exp)>=2 && !err)
        {
            try
            {
                //exp[1] = (exp[1]);
                //if(!dorat.israt)
                //    isr = false;
                tem = (gcd(numer(exp[0]),numer(exp[1])))/(lcm(denom(exp[0]),denom(exp[1])));
                exp.remove_first();
                exp.remove_first();
                exp.prepend(tem);
            }
            catch(std::invalid_argument){err = true; is_a<fail>(exp[0]);}

        }
        //if(isr)
        return exp[0];
        //else
        //    return evalf(exp[0]);
    }

    /** calculating lcm of list of expressions **/
    ex Lcm(lst exp)
    {
        bool err = false; //isr = true;
        ex tem;
        //dorat dorat; // avoiding double form
        //dorat.set();
        //exp[0] = dorat(exp[0]);
        //if(!dorat.israt)
        //   isr = false;
        while(nops(exp)>=2 && !err)
        {
            try
            {
                //exp[1] = dorat(exp[1]);
                //if(!dorat.israt)
                //   isr = false;
                tem = (lcm(numer(exp[0]),numer(exp[1])))/(gcd(denom(exp[0]),denom(exp[1])));
                exp.remove_first();
                exp.remove_first();
                exp.prepend(tem);
            }
            catch(std::invalid_argument){err = true; is_a<fail>(exp[0]);}

        }
        //if(isr)
        return exp[0];
        //else
        //   return evalf(exp[0]);
    }


    /** replacing I by _symb **/
    ex replaceI::expr_visitor(const ex& _e)
    {
        if (is_a<numeric>(_e) && !_e.info(info_flags::real))
        {
            return externSymbols.symb_*_e.imag_part() + _e.real_part();
        }
        return _e.map(*this);
    }
    //////////////////////////////////////////////////////////////////////////////////


    //////////////////////////////////////////////////////////////////////////////////

    ex symbol_finderc::expr_visitor(const ex& _e)
    {
        if (is_a<symbol>(_e))
        {
            symbols.insert(_e);
            return _e.map(*this);
        }

        return _e.map(*this);
    }
    //////////////////////////////////////////////////////////////////////////////////

    exset symbols(const ex& expr_)
    {
        symbol_finder.clear();
        symbol_finder.expr_visitor(expr_);
        return symbol_finder.symbols;
    }
    //////////////////////////////////////////////////////////////////////////////////
    /** collecting power of each base from pow argument, excludes similar power**/
    ex basepow_clt::expr_visitor(const ex& _e)
    {
        if (is_a<power>(_e) &&
            _e.op(0).has(_var))
        {
            lst tem = basepow[_e.op(0)];
            if(nops(tem))
            {
                const exset temset = exprchk;
                exprchk.insert(_e.op(1));
                if(temset.size() != exprchk.size())
                    basepow[_e.op(0)] = tem.append(_e.op(1));
            }
            else
                basepow[_e.op(0)] = (lst){_e.op(1)};
            return _e;
        }
        else if(is_a<symbol>(_e) &&
                 _e==_var)
        {
            lst tem = basepow[_e];
            if(nops(tem))
            {
                const exset temset = exprchk;
                exprchk.insert(_ex1);
                if(temset.size() != exprchk.size())
                    basepow[_e] = tem.append(_ex1);
            }
            else
                basepow[_e] = (lst){_e};
            return _e;
        }


        return _e.map(*this);
    }

    /** Checking polynomial with variable **/
    bool is_poly(const ex& _expr, const ex& _var)
    {
        bool polytype=true;
        for(auto itr=_expr.preorder_begin();itr!=_expr.preorder_end();itr++){
            if(is_a<power>(*itr) && (*itr).op(0).has(_var) &&
                ((((*itr).op(1)).info(info_flags::numeric) && !(*itr).op(1).info(info_flags::posint))
                 || !(*itr).op(1).info(info_flags::numeric)))
                polytype = false;
            if(is_a<ginacsym::function>((*itr)) && ((*itr).op(0).has(_var) || (nops((*itr)) > 1 && (*itr).op(1).has(_var))) )
                polytype = false;
        }

        return polytype;
    }

    /** Checking presence and type of functions with given variable and checking conjugate in equation **/
    ex funcpresent::expr_visitor(const ex& _e)
    {
        if(is_a<ginacsym::function>(_e) && nops(_e) == 1)
        {
            if(_e.op(0).has(_var))
            {
                funcwtvar.insert(_e);
                funcpresence = true;
            }
            else if((_e.op(0)) == conjugate(_e)) // avoiding conjugate as it gives error when factor
                funcpresence = true;
            else
                func.insert(_e);
        }
        else if(is_a<functions>(_e))
        {
            if(_e.has(_var))
                funcpresence = true;
        }

        if(is_a<power>(_e))
        {
            if((_e.op(1)).has(_var)) // avoiding solution variable in power
                varInPow = true;
        }


        return _e.map(*this);
    }

    /// doing conjugate free ///
    ex conjuFree::expr_visitor(const ex& _e)
    {
        if( nops(_e) == 1 && _e.op(0) == conjugate(_e) )
            return _e.op(0);
        else
            return _e.map(*this);
    }

    conjuFree conjuFreee;


    /// Checking polynomial with variable in fim (avoiding functions other than diff)///
    ex polycheckFim::expr_visitor(const ex& _e)
    {
        if(is_a<power>(_e) && _e.op(0).has(_var) && (_e.op(1)).info(info_flags::numeric)
            && !(_e).op(1).info(info_flags::posint))
            polytype = false;
        if(is_a<power>(_e) && _e.op(0).has(_var) && !(_e.op(1)).info(info_flags::numeric))
            polytype = false;
        if(is_a<ginacsym::function>(_e) && _e.op(0).has(_var) && !is_a<Diff>(_e) && !((_e.op(0)) == conjugate(_e)))
            polytype = false;

        return _e.map(*this);
    }

    /// Collecting power of a variable in fim (this function has been used for auto-evaluation of NValue in desolve.cpp )///
    ex powClt::expr_visitor(const ex& _e)
    {
        if(is_a<power>(_e) && _e.op(0) == _var)
            powers.push_back(_e.op(1));
        return _e.map(*this);
    }

    /** this function substitute generated symbols from exmap **/
    ex genSymbSubs(const ex& _e, const exmap& highDegSubsClt)
    {
        ex _y = _e;
        if(!highDegSubsClt.empty())
        {
            exmap reversed;
            for(auto itr=highDegSubsClt.begin();itr!=highDegSubsClt.end();itr++)
                reversed[itr->second]=(itr->first);

            _y=(_y.subs(reversed));
        }

        return _y;
    }

    /** Getting lst of coefficients from all terms where present _var.
isCltPowZero = true allow to get coefficients of _var^0. **/
    lst collectAllCoeff(const ex& _expr, const lst& _var, const bool& isCltPowZero, exmap& _varsWtcoeff)
    {
        ex coeffClt = _ex1, varsClt = _ex1;
        exmap varsWtcoeff;
        lst totalCoeffClt={};
        if(is_a<add>(_expr))
        {

            for(unsigned i = 0; i < nops(_expr); i++) // add
            {
                if(is_a<mul>(_expr.op(i)))
                {
                    for(unsigned j = 0; j < nops(_expr.op(i)); j++)
                    {
                        unsigned k = 0;
                        do
                        {
                            if(!_expr.op(i).op(j).has(_var.op(k)))
                            {
                                coeffClt = coeffClt*_expr.op(i).op(j);
                            }
                            else if(_expr.op(i).op(j).has(_var.op(k)))
                            {
                                varsClt = varsClt*_expr.op(i).op(j);
                            }

                            k++;

                        }while(k<nops(_var));
                    }
                }
                else
                {
                    unsigned k = 0;
                    do
                    {
                        if(!_expr.op(i).has(_var.op(k)))
                        {
                            coeffClt = coeffClt*_expr.op(i);
                        }
                        else if(_expr.op(i).has(_var.op(k)))
                        {
                            varsClt = varsClt*_expr.op(i);
                        }

                        k++;

                    }while(k<nops(_var));
                }

                if(!isCltPowZero && varsClt != _ex1)
                    varsWtcoeff[varsClt] = varsWtcoeff[varsClt]+coeffClt;
                else if(isCltPowZero)
                    varsWtcoeff[varsClt] = varsWtcoeff[varsClt]+coeffClt;
                coeffClt=_ex1;
                varsClt=_ex1;
            }


        }
        else
        {
            if(is_a<mul>(_expr))
            {
                for(unsigned j = 0; j < nops(_expr); j++)
                {
                    unsigned k = 0;
                    do
                    {
                        if(!_expr.op(j).has(_var.op(k)))
                        {
                            coeffClt = coeffClt*_expr.op(j);
                        }
                        else if(_expr.op(j).has(_var.op(k)))
                        {
                            varsClt = varsClt*_expr.op(j);
                        }

                        k++;

                    }while(k<nops(_var));
                }
            }
            else
            {
                unsigned k = 0;
                do
                {
                    if(!_expr.has(_var.op(k)))
                    {
                        coeffClt = coeffClt*_expr;
                    }
                    else if(_expr.has(_var.op(k)))
                    {
                        varsClt = varsClt*_expr;
                    }

                    k++;

                }while(k<nops(_var));
            }

            if(!isCltPowZero && varsClt != _ex1)
                varsWtcoeff[varsClt] = varsWtcoeff[varsClt]+coeffClt;
            else if(isCltPowZero)
                varsWtcoeff[varsClt] = varsWtcoeff[varsClt]+coeffClt;
            coeffClt=_ex1;
            varsClt=_ex1;

        }

        if(!varsWtcoeff.empty())
        {
            _varsWtcoeff=varsWtcoeff;

            for(auto itr = varsWtcoeff.begin(); itr != varsWtcoeff.end(); itr++)
            {
                totalCoeffClt.append(itr->second);
            }
        }

        return totalCoeffClt;
    }


    /** Getting numerator and denominator. **/
    ex Numer_Denom(const ex& _expr)
    {
        fracPowBasSubsE.set();
        const ex temexpr_=fracPowBasSubsE.expr_visitor(_expr);
        ex nude;
        lst nudeClt;
        nude = temexpr_.numer_denom();

        if(!fracPowBasSubsE.baseClt.empty())
        {
            nudeClt.append( genSymbSubs(nude.op(0),fracPowBasSubsE.baseClt));
            nudeClt.append(genSymbSubs(nude.op(1),fracPowBasSubsE.baseClt));
            fracPowBasSubsE.set();

            return nudeClt;
        }

        return nude;
    }

    /**Following function checks presence of functions (Ex: sin,cos,log,asin etc.)**/
    bool hasFunction(const ex& _expr)
    {
        for(const_preorder_iterator itr = _expr.preorder_begin(); itr != _expr.preorder_end(); itr++){
            if (is_a<function>(*itr)) {
                return true;
            }
        }

        return false;
    }

    /**collect all coefficients of x in polynomial or nonpolynomial expressions**/
    ex collectAllc::expr_visitor(const ex& e)
    {
        ma.clear();
        //if (e.is_polynomial(var)) {
        return (collect(e.to_polynomial(ma),var,distributed)).subs(ma).map(*this);
//        }
//        else {
//            return e.map(*this);
//        }
    }

//unsigned nonRatsubs::symnum=0;

}


//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////




