
/** @file integrate.cpp
 *
 *  Implementation of some basic integration process. **/

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

#include "add.h"
#include "fail.h"
#include "functions.h"
#include "mul.h"
#include "normal.h"
#include "utility.h"
#include "inifcns.h"
#include "simplify.h"
#include "inert.h"
#include "integrate.h"

using namespace std;

namespace ginacsym{
    //integratec integrate;
    /** finding constant terms in integrand **/
    /******************************************/
    ex integratec::find_const(const ex &e_) const
    {
        ex expr = _ex1;
        if (is_a<mul>(e_))
        {
            for(unsigned i = 0; i != nops(e_); i++ )
            {
                if (!e_.op(i).has(this->var))
                    expr = expr*e_.op(i);
            }
        }
        else
        {
            if (!e_.has(this->var))
                expr = e_;
        }
        return expr;
    }

    /** integration by parts method **/
    /**************************************/

    ex integratec::do_inte(const ex& expr_) const
    {
        if (!is_a<mul>(expr_))
            return func_inte(expr_,var,partial_num);

        exmap repls;

        //x^n*log(x)
        expr_.match(pow(var,wild(0))*log(var), repls);
        if (!repls.empty() && !repls[wild(0)].has(var) && repls[wild(0)] > _ex0)
            return pow(var,(_ex1 + repls[wild(0)]))*(_ex_1 + (_ex1 + repls[wild(0)])*log(var))/pow((1 +
                                                                                                           repls[wild(0)]),2);

        //exp(x)*sin(x)
        repls.clear();
        expr_.match(exp(wild(0))*sin(wild(1)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(this->var) && (repls[wild(0)]).degree(this->var) == 1
            && (repls[wild(1)]).is_polynomial(this->var) && (repls[wild(1)]).degree(this->var) == 1)
            return exp(repls[wild(0)])*(sin(repls[wild(1)])*(repls[wild(0)]).coeff(this->var, 1)-(repls[wild(1)]).coeff(this->var, 1)*cos(repls[wild(1)]))/(pow((repls[wild(0)]).coeff(this->var, 1),2)+pow((repls[wild(1)]).coeff(this->var, 1),2));

        //exp(x)*cos(x)
        repls.clear();
        expr_.match(exp(wild(0))*cos(wild(1)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(this->var) && (repls[wild(0)]).degree(this->var) == 1
            && (repls[wild(1)]).is_polynomial(this->var) && (repls[wild(1)]).degree(this->var) == 1)
            return exp(repls[wild(0)])*((repls[wild(1)]).coeff(this->var, 1)*sin(repls[wild(1)])+cos(repls[wild(1)])*(repls[wild(0)]).coeff(this->var, 1))/(pow((repls[wild(0)]).coeff(this->var, 1),2)+pow((repls[wild(1)]).coeff(this->var, 1),2));

        //sec(x)^2
        repls.clear();
        expr_.match(pow(sec(wild(0)),_ex2), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(this->var) && (repls[wild(0)]).degree(this->var) == 1)
            return  tan(repls[wild(0)])/repls[wild(0)].coeff(var);

        //csc(x)^2
        repls.clear();
        expr_.match(pow(csc(wild(0)),_ex2), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(this->var) && (repls[wild(0)]).degree(this->var) == 1)
            return  -cot(repls[wild(0)])/repls[wild(0)].coeff(var);

        //sec(x)*tan(x)
        repls.clear();
        expr_.match(sec(wild(0))*tan(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(this->var) && (repls[wild(0)]).degree(this->var) == 1)
            return  sec(repls[wild(0)])/(repls[wild(0)].coeff(var));

        //csc(x)*cot(x)
        repls.clear();
        expr_.match(csc(wild(0))*cot(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(this->var) && (repls[wild(0)]).degree(this->var) == 1)
            return  -csc(repls[wild(0)])/(repls[wild(0)].coeff(var));

        //sech(x)^2
        repls.clear();
        expr_.match(pow(sech(wild(0)),_ex2), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(this->var) && (repls[wild(0)]).degree(this->var) == 1)
            return  tanh(repls[wild(0)])/repls[wild(0)].coeff(var);

        //csch(x)^2
        repls.clear();
        expr_.match(pow(csch(wild(0)),_ex2), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(this->var) && (repls[wild(0)]).degree(this->var) == 1)
            return  -coth(repls[wild(0)])/repls[wild(0)].coeff(var);

        //sech(x)*tanh(x)
        repls.clear();
        expr_.match(sech(wild(0))*tanh(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(this->var) && (repls[wild(0)]).degree(this->var) == 1)
            return  -sech(repls[wild(0)])/(repls[wild(0)].coeff(var));

        //csch(x)*coth(x)
        repls.clear();
        expr_.match(csch(wild(0))*coth(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(this->var) && (repls[wild(0)]).degree(this->var) == 1)
            return  -csch(repls[wild(0)])/(repls[wild(0)].coeff(var));

        //Diff*u
        repls.clear();
        expr_.match(Diff(Diff(wild(0),wild(1),0), wild(1),1)*Diff(wild(0),wild(1),0), repls);
        if(!repls.empty())
        {
            if(repls[wild(1)] != var)
                return Integrate(expr_, this->var,partial_num);
            return pow(repls[wild(0)],2)/(2);
        }

        // Diff*u^n
        repls.clear();
        expr_.match(Diff(Diff(wild(0),wild(1),0),wild(1),1)*pow(Diff(wild(0),wild(1),0),wild(2)), repls);
        if(!repls.empty())
        {
            if(repls[wild(1)] != var)
                return Integrate(expr_, this->var,partial_num);
            return pow(repls[wild(0)],repls[wild(2)]+1)/(repls[wild(2)]+1);
        }

        //Diff*Diff
        repls.clear();
        expr_.match(Diff(Diff(wild(0),wild(1),0), wild(1), wild(2))*Diff(Diff(wild(0),wild(1),0), wild(1), wild(4)), repls);
        expr_.match(Diff(Diff(wild(0),wild(1),0), wild(1),wild(2))*Diff(wild(0),wild(1),0), repls);
        if (!repls.empty()){
            //avoiding integration of partial derivaives
            if(repls[wild(1)] != var)
                return Integrate(expr_, this->var,partial_num);

            vector<int> dordr;
            if(!(repls[wild(2)]).info(info_flags::integer))
            {
                dorat dorat; // avoiding double form
                dorat.set();
                if(!dorat.expr_visitor(repls[wild(2)]).info(info_flags::integer))
                    return dynallocate<fail>();
                dordr.push_back(ex_to<numeric>(dorat.expr_visitor(repls[wild(2)])).to_int());
            }
            else
                dordr.push_back(ex_to<numeric>(repls[wild(2)]).to_int());

            if(!(repls[wild(4)]).info(info_flags::integer))
            {
                dorat dorat; // avoiding double form
                dorat.set();
                if(!dorat.expr_visitor(repls[wild(4)]).info(info_flags::integer))
                    return dynallocate<fail>();
                dordr.push_back(ex_to<numeric>(dorat.expr_visitor(repls[wild(4)])).to_int());
            }
            else
                dordr.push_back(ex_to<numeric>(repls[wild(4)]).to_int());

            if((dordr[0] + dordr[1])%2 == 0)
                return Integrate(expr_, this->var,partial_num);

            sort(dordr.begin(), dordr.end());

            exmap rep, rep1;
            ex exmax, exmin;
            expr_.op(0).match(Diff(wild(5), wild(6), wild(7)), rep);

            int wild7int;
            if(!(rep[wild(7)]).info(info_flags::integer))
            {
                dorat dorat; // avoiding double form
                dorat.set();
                if(!dorat.expr_visitor(rep[wild(7)]).info(info_flags::integer))
                    return dynallocate<fail>();
                wild7int=ex_to<numeric>(dorat.expr_visitor(rep[wild(7)])).to_int();
            }
            else
                wild7int=ex_to<numeric>(rep[wild(7)]).to_int();

            if(wild7int == dordr[0])
            {
                exmin = expr_.op(0);
                exmax = expr_.op(1);
            }
            else
            {
                exmin = expr_.op(1);
                exmax = expr_.op(0);
            }

            rep.clear();

            exmin.match(Diff(wild(5), wild(6), wild(7)), rep);
            exmax.match(Diff(wild(5), wild(6), wild(7)), rep1);

            ex expr = _ex0;
            int imax = (dordr[1] - 1 - dordr[0])/2;

            for(int i = 0; i <= imax; i++)
            {
                if(i == imax)
                {
                    expr = expr + _ex1_2*pow(_ex_1, i)*Diff(rep[wild(5)], rep[wild(6)], rep[wild(7)] + i)*
                                      Diff(rep1[wild(5)], rep1[wild(6)], rep1[wild(7)] - 1 - i);
                }
                else
                {
                    expr = expr + pow(_ex_1, i)*Diff(rep[wild(5)], rep[wild(6)], rep[wild(7)] + i)*
                                      Diff(rep1[wild(5)], rep1[wild(6)], rep1[wild(7)] - 1 - i);
                }

            }
            rep.clear();
            rep1.clear();

            return expr;
        }


        repls.clear();
        //with x^n*Diff(wild(0)) funtions
        expr_.match(wild(0)*Diff(wild(1), wild(2), wild(3)), repls);
        //x^n*sin(a*x+b)
        expr_.match(wild(0)*sin(wild(1)), repls);
        //x^n*cos(a*x+b)
        expr_.match(wild(0)*cos(wild(1)), repls);
        //x^n*exp(a*x+b)
        expr_.match(wild(0)*exp(wild(1)), repls);

        if (!repls.empty())
        {
            //avoiding integration of partial derivaives
            if(expr_.has(Diff(wild(1), wild(2), wild(3))) && repls[wild(2)] != var)
                return Integrate(expr_, this->var,partial_num);

            ex funcexpr;

            funcexpr = Simplify(expand(expr_/repls[wild(0)]));

            if( !funcexpr.has(Diff(wild(0), wild(1), wild(2))) )
            {
                if (!repls[wild(0)].is_polynomial(this->var) || !repls[wild(1)].is_polynomial(this->var)
                    || !((repls[wild(1)]).degree(this->var) == 1))
                    return Integrate(expr_, this->var,partial_num);
            }
            else
            {
                if (!repls[wild(0)].is_polynomial(this->var))
                    return Integrate(expr_, this->var,partial_num);
            }

            ex expr1, expr2, expr = _ex0, constterm;
            exvector exvec1, exvec2;
            exvec1.push_back(repls[wild(0)]);
            expr1 = repls[wild(0)];
            expr2 = funcexpr;
            do
            {
                constterm = this->find_const(expr2);
                expr2 = constterm*func_inte( Simplify(expand(expr2/constterm )),var,partial_num);
                if (expr2.has(Integrate(wild(0), wild(1))) && exvec1.size() == 1)
                    return Integrate(expr_, this->var,partial_num);
                expr1 = diff(expr1, ex_to<symbol>(this->var));

                exvec1.push_back(expr1);
                exvec2.push_back(expr2);
            }while(expr1 != _ex0 && !expr2.has(Integrate(wild(0), wild(1))));

            auto it1 = exvec1.begin();
            auto it2 = exvec2.begin();

            for (size_t i = 0; i < exvec1.size() - 1; i++)
            {
                if (!((*next(it2, i)).has(Integrate(wild(0), wild(1)))))
                    expr = expr + pow(_ex_1, i)*(*next(it1, i))*(*next(it2, i));
                else
                    expr = expr + pow(_ex_1, i)*Integrate((*next(it1, i))*(*next(it2, i)), this->var,partial_num);
            }
            return expr;
        }



        return Integrate(expr_, this->var,partial_num);
        //with Integrate
    }

    exvector Liate(const ex& expr_, const ex& var)
    {
        //soting mul components of expr_ according to LIATE rule of thumb
        exvector L1,L2,L3,L4,L5,//log

            IS1,IS2,IS3,IS4,IS5,//asin
            IC1,IC2,IC3,IC4,IC5,//acos
            IT1,IT2,IT3,IT4,IT5,//atan
            ICS1,ICS2,ICS3,ICS4,ICS5,//acsc
            ISE1,ISE2,ISE3,ISE4,ISE5,//asec
            ICO1,ICO2,ICO3,ICO4,ICO5,//acot

            ISH1,ISH2,ISH3,ISH4,ISH5,//asinh
            ICH1,ICH2,ICH3,ICH4,ICH5,//acosh
            ITH1,ITH2,ITH3,ITH4,ITH5,//atanh
            ICSH1,ICSH2,ICSH3,ICSH4,ICSH5,//acsch
            ISEH1,ISEH2,ISEH3,ISEH4,ISEH5,//asech
            ICOH1,ICOH2,ICOH3,ICOH4,ICOH5,//acoth

            AP1,AP2,AP3,AP4,//x^n
            AR1,AR2,AR3,AR4,//1/(a*x^n+....+c)^m

            TS1,TS2,TS3,TS4,TS5,//sin
            TC1,TC2,TC3,TC4,TC5,//cos
            TT1,TT2,TT3,TT4,TT5,//tan
            TCS1,TCS2,TCS3,TCS4,TCS5,//csc
            TSE1,TSE2,TSE3,TSE4,TSE5,//sec
            TCO1,TCO2,TCO3,TCO4,TCO5,//cot

            TSH1,TSH2,TSH3,TSH4,TSH5,//sinh
            TCH1,TCH2,TCH3,TCH4,TCH5,//cosh
            TTH1,TTH2,TTH3,TTH4,TTH5,//tanh
            TCSH1,TCSH2,TCSH3,TCSH4,TCSH5,//csch
            TSEH1,TSEH2,TSEH3,TSEH4,TSEH5,//sech
            TCOH1,TCOH2,TCOH3,TCOH4,TCOH5,//coth

            E1,E2,E3,E4,E5,//exp

            OTHERS,//OTHER FUNCTION

            LIATE;
        //cout<<expr_<<endl;
        exmap ma;
        if (is_a<mul>(expr_)) {
            //cout<<expr_<<endl;

            for(const_iterator itr=expr_.begin();itr!=expr_.end();++itr){
                if (!(*itr).has(var)) {//avoiding symb_
                    continue;
                }

                ma.clear();
                //cout<<*itr<<endl;
                ////LOGARITHM FUNCTION/////
                if (is_ex_the_function(*itr,log)) {// log function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//log(var*a+b)
                        L1.push_back(*itr);
                    }
                    else {
                        L2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(log(wild(0)),wild(1)))) {// log function with power, Ex: (log(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(log(var))^2
                        L3.push_back(*itr);
                    }
                    else {//(log(var^2))^2
                        L4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(log(wild(0)))) {
                    L5.push_back(*itr);
                    continue;
                }

                ////INVERSE TRIGONMETRIC FUNCTION/////
                /// arcsin
                ma.clear();
                if (is_ex_the_function(*itr,asin)) {// asin function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//asin(var)
                        IS1.push_back(*itr);
                    }
                    else {//asin(var^2)
                        IS2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(asin(wild(0)),wild(1)))) {// asin function with power, Ex: (asin(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(asin(var))^2
                        IS3.push_back(*itr);
                    }
                    else {//(asin(var^2))^2
                        IS4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(asin(wild(0)))) {
                    IS5.push_back(*itr);
                    continue;
                }

                //arccos
                ma.clear();
                if (is_ex_the_function(*itr,acos)) {// acos function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//acos(var)
                        IC1.push_back(*itr);
                    }
                    else {//acos(var^2)
                        IC2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(acos(wild(0)),wild(1)))) {// acos function with power, Ex: (acos(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(acos(var))^2
                        IC3.push_back(*itr);
                    }
                    else {//(acos(var^2))^2
                        IC4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(acos(wild(0)))) {
                    IC5.push_back(*itr);
                    continue;
                }

                //arctan
                ma.clear();
                if (is_ex_the_function(*itr,atan)) {// atan function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//atan(var)
                        IT1.push_back(*itr);
                    }
                    else {//atan(var^2)
                        IT2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(atan(wild(0)),wild(1)))) {// atan function with power, Ex: (atan(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(atan(var))^2
                        IT3.push_back(*itr);
                    }
                    else {//(atan(var^2))^2
                        IT4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(atan(wild(0)))) {
                    IT5.push_back(*itr);
                    continue;
                }

                //arccsc
                ma.clear();
                if (is_ex_the_function(*itr,acsc)) {// acsc function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//acsc(var)
                        ICS1.push_back(*itr);
                    }
                    else {//acsc(var^2)
                        ICS2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(acsc(wild(0)),wild(1)))) {// acsc function with power, Ex: (acsc(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(acsc(var))^2
                        ICS3.push_back(*itr);
                    }
                    else {//(acsc(var^2))^2
                        ICS4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(acsc(wild(0)))) {
                    ICS5.push_back(*itr);
                    continue;
                }

                //arcsec
                ma.clear();
                if (is_ex_the_function(*itr,asec)) {// asec function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//asec(var)
                        ISE1.push_back(*itr);
                    }
                    else {//asec(var^2)
                        ISE2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(asec(wild(0)),wild(1)))) {// asec function with power, Ex: (asec(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(asec(var))^2
                        ISE3.push_back(*itr);
                    }
                    else {//(asec(var^2))^2
                        ISE4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(asec(wild(0)))) {
                    ISE5.push_back(*itr);
                    continue;
                }

                //arccot
                ma.clear();
                if (is_ex_the_function(*itr,acot)) {// acot function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//acot(var)
                        ICO1.push_back(*itr);
                    }
                    else {//acot(var^2)
                        ICO2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(acot(wild(0)),wild(1)))) {// acot function with power, Ex: (acot(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(acot(var))^2
                        ICO3.push_back(*itr);
                    }
                    else {//(acot(var^2))^2
                        ICO4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(acot(wild(0)))) {
                    ICO5.push_back(*itr);
                    continue;
                }

                /////////////Inverse hypebolic///////////////////

                /// arcsinh
                ma.clear();
                if (is_ex_the_function(*itr,asinh)) {// asinh function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//asinh(var)
                        ISH1.push_back(*itr);
                    }
                    else {//asinh(var^2)
                        ISH2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(asinh(wild(0)),wild(1)))) {// asinh function with power, Ex: (asinh(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(asinh(var))^2
                        ISH3.push_back(*itr);
                    }
                    else {//(asinh(var^2))^2
                        ISH4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(asinh(wild(0)))) {
                    ISH5.push_back(*itr);
                    continue;
                }

                //arccosh
                ma.clear();
                if (is_ex_the_function(*itr,acosh)) {// acosh function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//acosh(var)
                        ICH1.push_back(*itr);
                    }
                    else {//acosh(var^2)
                        ICH2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(acosh(wild(0)),wild(1)))) {// acosh function with power, Ex: (acosh(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(acosh(var))^2
                        ICH3.push_back(*itr);
                    }
                    else {//(acosh(var^2))^2
                        ICH4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(acosh(wild(0)))) {
                    ICH5.push_back(*itr);
                    continue;
                }


                //arctanh
                ma.clear();
                if (is_ex_the_function(*itr,atanh)) {// atanh function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//atanh(var)
                        ITH1.push_back(*itr);
                    }
                    else {//atanh(var^2)
                        ITH2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(atanh(wild(0)),wild(1)))) {// atanh function with power, Ex: (atanh(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(atanh(var))^2
                        ITH3.push_back(*itr);
                    }
                    else {//(atanh(var^2))^2
                        ITH4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(atanh(wild(0)))) {
                    ITH5.push_back(*itr);
                    continue;
                }

                //arccsch
                ma.clear();
                if (is_ex_the_function(*itr,acsch)) {// acsch function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//acsch(var)
                        ICSH1.push_back(*itr);
                    }
                    else {//acsch(var^2)
                        ICSH2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(acsch(wild(0)),wild(1)))) {// acsch function with power, Ex: (acsch(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(acsch(var))^2
                        ICSH3.push_back(*itr);
                    }
                    else {//(acsch(var^2))^2
                        ICSH4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(acsch(wild(0)))) {
                    ICSH5.push_back(*itr);
                    continue;
                }

                //arcsech
                ma.clear();
                if (is_ex_the_function(*itr,asech)) {// asech function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//asech(var)
                        ISEH1.push_back(*itr);
                    }
                    else {//asech(var^2)
                        ISEH2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(asech(wild(0)),wild(1)))) {// asech function with power, Ex: (asech(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(asech(var))^2
                        ISEH3.push_back(*itr);
                    }
                    else {//(asech(var^2))^2
                        ISEH4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(asech(wild(0)))) {
                    ISEH5.push_back(*itr);
                    continue;
                }

                //arccoth
                ma.clear();
                if (is_ex_the_function(*itr,acoth)) {// acoth function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//acoth(var)
                        ICOH1.push_back(*itr);
                    }
                    else {//acoth(var^2)
                        ICOH2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(acoth(wild(0)),wild(1)))) {// acoth function with power, Ex: (acoth(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(acoth(var))^2
                        ICOH3.push_back(*itr);
                    }
                    else {//(acoth(var^2))^2
                        ICOH4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(acoth(wild(0)))) {
                    ICOH5.push_back(*itr);
                    continue;
                }

                ///ALGEBRAIC FUNCTION//////////
                ma.clear();
                if ((*itr).is_equal(var)) {// x
                    AP1.push_back(*itr);
                    continue;
                }
                else if ((*itr).match(pow(var,wild(0)),ma) &&
                         !ma[wild(0)].has(var)) {// x^n
                    AP2.push_back(*itr);
                    continue;
                }
                else if(!hasFunction(*itr)){AP3.push_back(*itr);}

                //EXPONENTIAL FUNCTION///
                ma.clear();
                if ((*itr).match(exp(wild(0)),ma) &&
                    !ma[wild(0)].has(var)) {// exp(wild(0))
                    E1.push_back(*itr);
                    continue;
                }
                else if ((*itr).has(exp(wild(0)))){
                    E2.push_back(*itr);
                    continue;
                }

                ///TRIGONMETRIC FUNCTION///////
                /// sin
                ma.clear();
                if (is_ex_the_function(*itr,sin)) {// sin function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//sin(var)

                        TS1.push_back(*itr);
                    }
                    else {//sin(var^2)
                        TS2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(sin(wild(0)),wild(1)))) {// sin function with power, Ex: (sin(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(sin(var))^2
                        TS3.push_back(*itr);
                    }
                    else {//(sin(var^2))^2
                        TS4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(sin(wild(0)))) {
                    TS5.push_back(*itr);
                    continue;
                }

                /// cos
                ma.clear();
                if (is_ex_the_function(*itr,cos)) {// cos function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//cos(var)

                        TC1.push_back(*itr);
                    }
                    else {//cos(var^2)
                        TC2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(cos(wild(0)),wild(1)))) {// cos function with power, Ex: (cos(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(cos(var))^2
                        TC3.push_back(*itr);
                    }
                    else {//(cos(var^2))^2
                        TC4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(cos(wild(0)))) {
                    TC5.push_back(*itr);
                    continue;
                }

                /// tan
                ma.clear();
                if (is_ex_the_function(*itr,tan)) {// tan function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//tan(var)

                        TT1.push_back(*itr);
                    }
                    else {//tan(var^2)
                        TT2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(tan(wild(0)),wild(1)))) {// tan function with power, Ex: (tan(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(tan(var))^2
                        TT3.push_back(*itr);
                    }
                    else {//(tan(var^2))^2
                        TT4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(tan(wild(0)))) {
                    TT5.push_back(*itr);
                    continue;
                }


                /// csc
                ma.clear();
                if (is_ex_the_function(*itr,csc)) {// csc function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//csc(var)

                        TCS1.push_back(*itr);
                    }
                    else {//csc(var^2)
                        TCS2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(csc(wild(0)),wild(1)),ma)) {// csc function with power, Ex: (csc(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(csc(var))^2
                        if(ma[wild(1)]>_ex2){
                            TCS3.push_back(pow(csc(ma[wild(0)]),ma[wild(1)]-2));//csc(x)^n,n>2
                            TCS3.push_back(pow(csc(ma[wild(0)]),2));
                        }
                        else TCS3.push_back(pow(csc(ma[wild(0)]),ma[wild(1)]));//csc(x)^2
                    }
                    else {//(csc(var^2))^2
                        TCS4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(csc(wild(0)))) {
                    TCS5.push_back(*itr);
                    continue;
                }

                /// sec
                ma.clear();
                if (is_ex_the_function(*itr,sec)) {// sec function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//sec(var)

                        TSE1.push_back(*itr);
                    }
                    else {//sec(var^2)
                        TSE2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(sec(wild(0)),wild(1)),ma)) {// sec function with power, Ex: (sec(var))^2
                    if ((*itr).op(0).op(0).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(sec(var))^2
                        if(ma[wild(1)]>_ex2){
                            TSE3.push_back(pow(sec(ma[wild(0)]),ma[wild(1)]-2));//sec(x)^n,n>2
                            TSE3.push_back(pow(sec(ma[wild(0)]),2));
                        }
                        else TSE3.push_back(pow(sec(ma[wild(0)]),ma[wild(1)]));//sec(x)^2
                    }
                    else {//(sec(var^2))^2
                        TSE4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(sec(wild(0)))) {
                    TSE5.push_back(*itr);
                    continue;
                }

                /// cot
                ma.clear();
                if (is_ex_the_function(*itr,cot)) {// cot function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//cot(var)

                        TCO1.push_back(*itr);
                    }
                    else {//cot(var^2)
                        TCO2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(cot(wild(0)),wild(1)))) {// cot function with power, Ex: (cot(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(cot(var))^2
                        TCO3.push_back(*itr);
                    }
                    else {//(cot(var^2))^2
                        TCO4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(cot(wild(0)))) {
                    TCO5.push_back(*itr);
                    continue;
                }



                ////////////HYPERBOLIC////////////
                /// sinh
                ma.clear();
                if (is_ex_the_function(*itr,sinh)) {// sinh function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//sinh(var)

                        TSH1.push_back(*itr);
                    }
                    else {//sinh(var^2)
                        TSH2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(sinh(wild(0)),wild(1)))) {// sinh function with power, Ex: (sinh(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(sinh(var))^2
                        TSH3.push_back(*itr);
                    }
                    else {//(sinh(var^2))^2
                        TSH4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(sinh(wild(0)))) {
                    TSH5.push_back(*itr);
                    continue;
                }

                /// cosh
                ma.clear();
                if (is_ex_the_function(*itr,cosh)) {// cosh function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//cosh(var)

                        TCH1.push_back(*itr);
                    }
                    else {//cosh(var^2)
                        TCH2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(cosh(wild(0)),wild(1)))) {// cosh function with power, Ex: (cosh(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(cosh(var))^2
                        TCH3.push_back(*itr);
                    }
                    else {//(cosh(var^2))^2
                        TCH4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(cosh(wild(0)))) {
                    TCH5.push_back(*itr);
                    continue;
                }


                /// tanh
                ma.clear();
                if (is_ex_the_function(*itr,tanh)) {// tanh function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//tanh(var)

                        TTH1.push_back(*itr);
                    }
                    else {//tanh(var^2)
                        TTH2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(tanh(wild(0)),wild(1)))) {// tanh function with power, Ex: (tanh(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(tanh(var))^2
                        TTH3.push_back(*itr);
                    }
                    else {//(tanh(var^2))^2
                        TTH4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(tanh(wild(0)))) {
                    TTH5.push_back(*itr);
                    continue;
                }

                /// csch
                ma.clear();
                if (is_ex_the_function(*itr,csch)) {// csch function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//csch(var)

                        TCSH1.push_back(*itr);
                    }
                    else {//csch(var^2)
                        TCSH2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(csch(wild(0)),wild(1)))) {// csch function with power, Ex: (csch(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(csch(var))^2
                        TCSH3.push_back(*itr);
                    }
                    else {//(csch(var^2))^2
                        TCSH4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(csch(wild(0)))) {
                    TCSH5.push_back(*itr);
                    continue;
                }

                /// sech
                ma.clear();
                if (is_ex_the_function(*itr,sech)) {// sech function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//sech(var)

                        TSEH1.push_back(*itr);
                    }
                    else {//sech(var^2)
                        TSEH2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(sech(wild(0)),wild(1)),ma)) {// sech function with power, Ex: (sech(var))^2
                    if ((*itr).op(0).op(0).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(sech(var))^2
                        if(ma[wild(1)]>_ex2){
                            TSEH3.push_back(pow(sech(ma[wild(0)]),ma[wild(1)]-2));//sech^n(x),n>2
                            TSEH3.push_back(pow(sech(ma[wild(0)]),2));
                        }
                        else TSEH3.push_back(pow(sech(ma[wild(0)]),ma[wild(1)]));//sech^2(x)
                    }
                    else {//(sech(var^2))^2
                        TSEH4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(sech(wild(0)))) {
                    TSEH5.push_back(*itr);
                    continue;
                }

                /// coth
                ma.clear();
                if (is_ex_the_function(*itr,coth)) {// coth function without power
                    if (((*itr).op(0)).is_polynomial(var) && degree((*itr).op(0),var)==1) {//coth(var)

                        TCOH1.push_back(*itr);
                    }
                    else {//coth(var^2)
                        TCOH2.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).match(pow(coth(wild(0)),wild(1)))) {// coth function with power, Ex: (coth(var))^2
                    if (((*itr).op(0).op(0)).is_polynomial(var) && degree((*itr).op(0).op(0),var)==1) {//(coth(var))^2
                        TCOH3.push_back(*itr);
                    }
                    else {//(coth(var^2))^2
                        TCOH4.push_back(*itr);
                    }
                    continue;
                }
                else if ((*itr).has(coth(wild(0)))) {
                    TCOH5.push_back(*itr);
                    continue;
                }


                OTHERS.push_back(*itr);

            }
        }



        ///COLLECTING IN LIATE//////
        /// log
        if (!L1.empty()) {
            copy(L1.begin(),L1.end(),back_inserter(LIATE));
        }
        if (!L2.empty()) {
            copy(L2.begin(),L2.end(),back_inserter(LIATE));
        }
        if (!L3.empty()) {
            copy(L3.begin(),L3.end(),back_inserter(LIATE));
        }
        if (!L4.empty()) {
            copy(L4.begin(),L4.end(),back_inserter(LIATE));
        }
        if (!L5.empty()) {
            copy(L5.begin(),L5.end(),back_inserter(LIATE));
        }

        //arcsin
        if (!IS1.empty()) {
            copy(IS1.begin(),IS1.end(),back_inserter(LIATE));
        }
        if (!IS2.empty()) {
            copy(IS2.begin(),IS2.end(),back_inserter(LIATE));
        }
        if (!IS3.empty()) {
            copy(IS3.begin(),IS3.end(),back_inserter(LIATE));
        }
        if (!IS4.empty()) {
            copy(IS4.begin(),IS4.end(),back_inserter(LIATE));
        }
        if (!IS5.empty()) {
            copy(IS5.begin(),IS5.end(),back_inserter(LIATE));
        }

        //arccos
        if (!IC1.empty()) {
            copy(IC1.begin(),IC1.end(),back_inserter(LIATE));
        }
        if (!IC2.empty()) {
            copy(IC2.begin(),IC2.end(),back_inserter(LIATE));
        }
        if (!IC3.empty()) {
            copy(IC3.begin(),IC3.end(),back_inserter(LIATE));
        }
        if (!IC4.empty()) {
            copy(IC4.begin(),IC4.end(),back_inserter(LIATE));
        }
        if (!IC5.empty()) {
            copy(IC5.begin(),IC5.end(),back_inserter(LIATE));
        }

        //arctan
        if (!IT1.empty()) {
            copy(IT1.begin(),IT1.end(),back_inserter(LIATE));
        }
        if (!IT2.empty()) {
            copy(IT2.begin(),IT2.end(),back_inserter(LIATE));
        }
        if (!IT3.empty()) {
            copy(IT3.begin(),IT3.end(),back_inserter(LIATE));
        }
        if (!IT4.empty()) {
            copy(IT4.begin(),IT4.end(),back_inserter(LIATE));
        }
        if (!IT5.empty()) {
            copy(IT5.begin(),IT5.end(),back_inserter(LIATE));
        }

        //arccsc
        if (!ICS1.empty()) {
            copy(ICS1.begin(),ICS1.end(),back_inserter(LIATE));
        }
        if (!ICS2.empty()) {
            copy(ICS2.begin(),ICS2.end(),back_inserter(LIATE));
        }
        if (!ICS3.empty()) {
            copy(ICS3.begin(),ICS3.end(),back_inserter(LIATE));
        }
        if (!ICS4.empty()) {
            copy(ICS4.begin(),ICS4.end(),back_inserter(LIATE));
        }
        if (!ICS5.empty()) {
            copy(ICS5.begin(),ICS5.end(),back_inserter(LIATE));
        }

        //arcsec
        if (!ISE1.empty()) {
            copy(ISE1.begin(),ISE1.end(),back_inserter(LIATE));
        }
        if (!ISE2.empty()) {
            copy(ISE2.begin(),ISE2.end(),back_inserter(LIATE));
        }
        if (!ISE3.empty()) {
            copy(ISE3.begin(),ISE3.end(),back_inserter(LIATE));
        }
        if (!ISE4.empty()) {
            copy(ISE4.begin(),ISE4.end(),back_inserter(LIATE));
        }
        if (!ISE5.empty()) {
            copy(ISE5.begin(),ISE5.end(),back_inserter(LIATE));
        }

        //arccot
        if (!ICO1.empty()) {
            copy(ICO1.begin(),ICO1.end(),back_inserter(LIATE));
        }
        if (!ICO2.empty()) {
            copy(ICO2.begin(),ICO2.end(),back_inserter(LIATE));
        }
        if (!ICO3.empty()) {
            copy(ICO3.begin(),ICO3.end(),back_inserter(LIATE));
        }
        if (!ICO4.empty()) {
            copy(ICO4.begin(),ICO4.end(),back_inserter(LIATE));
        }
        if (!ICO5.empty()) {
            copy(ICO5.begin(),ICO5.end(),back_inserter(LIATE));
        }

        //arcsinh
        if (!ISH1.empty()) {
            copy(ISH1.begin(),ISH1.end(),back_inserter(LIATE));
        }
        if (!ISH2.empty()) {
            copy(ISH2.begin(),ISH2.end(),back_inserter(LIATE));
        }
        if (!ISH3.empty()) {
            copy(ISH3.begin(),ISH3.end(),back_inserter(LIATE));
        }
        if (!ISH4.empty()) {
            copy(ISH4.begin(),ISH4.end(),back_inserter(LIATE));
        }
        if (!ISH5.empty()) {
            copy(ISH5.begin(),ISH5.end(),back_inserter(LIATE));
        }

        //arccosh
        if (!ICOH1.empty()) {
            copy(ICOH1.begin(),ICOH1.end(),back_inserter(LIATE));
        }
        if (!ICOH2.empty()) {
            copy(ICOH2.begin(),ICOH2.end(),back_inserter(LIATE));
        }
        if (!ICOH3.empty()) {
            copy(ICOH3.begin(),ICOH3.end(),back_inserter(LIATE));
        }
        if (!ICOH4.empty()) {
            copy(ICOH4.begin(),ICOH4.end(),back_inserter(LIATE));
        }
        if (!ICOH5.empty()) {
            copy(ICOH5.begin(),ICOH5.end(),back_inserter(LIATE));
        }

        //arctanh
        if (!ITH1.empty()) {
            copy(ITH1.begin(),ITH1.end(),back_inserter(LIATE));
        }
        if (!ITH2.empty()) {
            copy(ITH2.begin(),ITH2.end(),back_inserter(LIATE));
        }
        if (!ITH3.empty()) {
            copy(ITH3.begin(),ITH3.end(),back_inserter(LIATE));
        }
        if (!ITH4.empty()) {
            copy(ITH4.begin(),ITH4.end(),back_inserter(LIATE));
        }
        if (!ITH5.empty()) {
            copy(ITH5.begin(),ITH5.end(),back_inserter(LIATE));
        }

        //arccsch
        if (!ICSH1.empty()) {
            copy(ICSH1.begin(),ICSH1.end(),back_inserter(LIATE));
        }
        if (!ICSH2.empty()) {
            copy(ICSH2.begin(),ICSH2.end(),back_inserter(LIATE));
        }
        if (!ICSH3.empty()) {
            copy(ICSH3.begin(),ICSH3.end(),back_inserter(LIATE));
        }
        if (!ICSH4.empty()) {
            copy(ICSH4.begin(),ICSH4.end(),back_inserter(LIATE));
        }
        if (!ICSH5.empty()) {
            copy(ICSH5.begin(),ICSH5.end(),back_inserter(LIATE));
        }

        //arcsech
        if (!ISEH1.empty()) {
            copy(ISEH1.begin(),ISEH1.end(),back_inserter(LIATE));
        }
        if (!ISEH2.empty()) {
            copy(ISEH2.begin(),ISEH2.end(),back_inserter(LIATE));
        }
        if (!ISEH3.empty()) {
            copy(ISEH3.begin(),ISEH3.end(),back_inserter(LIATE));
        }
        if (!ISEH4.empty()) {
            copy(ISEH4.begin(),ISEH4.end(),back_inserter(LIATE));
        }
        if (!ISEH5.empty()) {
            copy(ISEH5.begin(),ISEH5.end(),back_inserter(LIATE));
        }

        //arccoth
        if (!ICOH1.empty()) {
            copy(ICOH1.begin(),ICOH1.end(),back_inserter(LIATE));
        }
        if (!ICOH2.empty()) {
            copy(ICOH2.begin(),ICOH2.end(),back_inserter(LIATE));
        }
        if (!ICOH3.empty()) {
            copy(ICOH3.begin(),ICOH3.end(),back_inserter(LIATE));
        }
        if (!ICOH4.empty()) {
            copy(ICOH4.begin(),ICOH4.end(),back_inserter(LIATE));
        }
        if (!ICOH5.empty()) {
            copy(ICOH5.begin(),ICOH5.end(),back_inserter(LIATE));
        }

        //algebraic
        if (!AP1.empty()) {
            copy(AP1.begin(),AP1.end(),back_inserter(LIATE));
        }
        if (!AP2.empty()) {
            copy(AP2.begin(),AP2.end(),back_inserter(LIATE));
        }
        if (!AP3.empty()) {
            copy(AP3.begin(),AP3.end(),back_inserter(LIATE));
        }


        //exp
        if (!E1.empty()) {
            copy(E1.begin(),E1.end(),back_inserter(LIATE));
        }
        if (!E2.empty()) {
            copy(E2.begin(),E2.end(),back_inserter(LIATE));
        }

        //sin
        if (!TS1.empty()) {
            copy(TS1.begin(),TS1.end(),back_inserter(LIATE));
        }
        if (!TS2.empty()) {
            copy(TS2.begin(),TS2.end(),back_inserter(LIATE));
        }
        if (!TS3.empty()) {
            copy(TS3.begin(),TS3.end(),back_inserter(LIATE));
        }
        if (!TS4.empty()) {
            copy(TS4.begin(),TS4.end(),back_inserter(LIATE));
        }
        if (!TS5.empty()) {
            copy(TS5.begin(),TS5.end(),back_inserter(LIATE));
        }

        //cos
        if (!TC1.empty()) {
            copy(TC1.begin(),TC1.end(),back_inserter(LIATE));
        }
        if (!TC2.empty()) {
            copy(TC2.begin(),TC2.end(),back_inserter(LIATE));
        }
        if (!TC3.empty()) {
            copy(TC3.begin(),TC3.end(),back_inserter(LIATE));
        }
        if (!TC4.empty()) {
            copy(TC4.begin(),TC4.end(),back_inserter(LIATE));
        }
        if (!TC5.empty()) {
            copy(TC5.begin(),TC5.end(),back_inserter(LIATE));
        }

        //tan
        if (!TT1.empty()) {
            copy(TT1.begin(),TT1.end(),back_inserter(LIATE));
        }
        if (!TT2.empty()) {
            copy(TT2.begin(),TT2.end(),back_inserter(LIATE));
        }
        if (!TT3.empty()) {
            copy(TT3.begin(),TT3.end(),back_inserter(LIATE));
        }
        if (!TT4.empty()) {
            copy(TT4.begin(),TT4.end(),back_inserter(LIATE));
        }
        if (!TT5.empty()) {
            copy(TT5.begin(),TT5.end(),back_inserter(LIATE));
        }

        //csc
        if (!TCS1.empty()) {
            copy(TCS1.begin(),TCS1.end(),back_inserter(LIATE));
        }
        if (!TCS2.empty()) {
            copy(TCS2.begin(),TCS2.end(),back_inserter(LIATE));
        }
        if (!TCS3.empty()) {
            copy(TCS3.begin(),TCS3.end(),back_inserter(LIATE));
        }
        if (!TCS4.empty()) {
            copy(TCS4.begin(),TCS4.end(),back_inserter(LIATE));
        }
        if (!TCS5.empty()) {
            copy(TCS5.begin(),TCS5.end(),back_inserter(LIATE));
        }

        //sec
        if (!TSE1.empty()) {
            copy(TSE1.begin(),TSE1.end(),back_inserter(LIATE));
        }
        if (!TSE2.empty()) {
            copy(TSE2.begin(),TSE2.end(),back_inserter(LIATE));
        }
        if (!TSE3.empty()) {
            copy(TSE3.begin(),TSE3.end(),back_inserter(LIATE));
        }
        if (!TSE4.empty()) {
            copy(TSE4.begin(),TSE4.end(),back_inserter(LIATE));
        }
        if (!TSE5.empty()) {
            copy(TSE5.begin(),TSE5.end(),back_inserter(LIATE));
        }

        //cot
        if (!TCO1.empty()) {
            copy(TCO1.begin(),TCO1.end(),back_inserter(LIATE));
        }
        if (!TCO2.empty()) {
            copy(TCO2.begin(),TCO2.end(),back_inserter(LIATE));
        }
        if (!TCO3.empty()) {
            copy(TCO3.begin(),TCO3.end(),back_inserter(LIATE));
        }
        if (!TCO4.empty()) {
            copy(TCO4.begin(),TCO4.end(),back_inserter(LIATE));
        }
        if (!TCO5.empty()) {
            copy(TCO5.begin(),TCO5.end(),back_inserter(LIATE));
        }

        //sinh
        if (!TSH1.empty()) {
            copy(TSH1.begin(),TSH1.end(),back_inserter(LIATE));
        }
        if (!TSH2.empty()) {
            copy(TSH2.begin(),TSH2.end(),back_inserter(LIATE));
        }
        if (!TSH3.empty()) {
            copy(TSH3.begin(),TSH3.end(),back_inserter(LIATE));
        }
        if (!TSH4.empty()) {
            copy(TSH4.begin(),TSH4.end(),back_inserter(LIATE));
        }
        if (!TSH5.empty()) {
            copy(TSH5.begin(),TSH5.end(),back_inserter(LIATE));
        }

        //cosh
        if (!TCH1.empty()) {
            copy(TCH1.begin(),TCH1.end(),back_inserter(LIATE));
        }
        if (!TCH2.empty()) {
            copy(TCH2.begin(),TCH2.end(),back_inserter(LIATE));
        }
        if (!TCH3.empty()) {
            copy(TCH3.begin(),TCH3.end(),back_inserter(LIATE));
        }
        if (!TCH4.empty()) {
            copy(TCH4.begin(),TCH4.end(),back_inserter(LIATE));
        }
        if (!TCH5.empty()) {
            copy(TCH5.begin(),TCH5.end(),back_inserter(LIATE));
        }

        //tanh
        if (!TTH1.empty()) {
            copy(TTH1.begin(),TTH1.end(),back_inserter(LIATE));
        }
        if (!TTH2.empty()) {
            copy(TTH2.begin(),TTH2.end(),back_inserter(LIATE));
        }
        if (!TTH3.empty()) {
            copy(TTH3.begin(),TTH3.end(),back_inserter(LIATE));
        }
        if (!TTH4.empty()) {
            copy(TTH4.begin(),TTH4.end(),back_inserter(LIATE));
        }
        if (!TTH5.empty()) {
            copy(TTH5.begin(),TTH5.end(),back_inserter(LIATE));
        }

        //csch
        if (!TCSH1.empty()) {
            copy(TCSH1.begin(),TCSH1.end(),back_inserter(LIATE));
        }
        if (!TCSH2.empty()) {
            copy(TCSH2.begin(),TCSH2.end(),back_inserter(LIATE));
        }
        if (!TCSH3.empty()) {
            copy(TCSH3.begin(),TCSH3.end(),back_inserter(LIATE));
        }
        if (!TCSH4.empty()) {
            copy(TCSH4.begin(),TCSH4.end(),back_inserter(LIATE));
        }
        if (!TCSH5.empty()) {
            copy(TCSH5.begin(),TCSH5.end(),back_inserter(LIATE));
        }

        //sech
        if (!TSEH1.empty()) {
            copy(TSEH1.begin(),TSEH1.end(),back_inserter(LIATE));
        }
        if (!TSEH2.empty()) {
            copy(TSEH2.begin(),TSEH2.end(),back_inserter(LIATE));
        }
        if (!TSEH3.empty()) {
            copy(TSEH3.begin(),TSEH3.end(),back_inserter(LIATE));
        }
        if (!TSEH4.empty()) {
            copy(TSEH4.begin(),TSEH4.end(),back_inserter(LIATE));
        }
        if (!TSEH5.empty()) {
            copy(TSEH5.begin(),TSEH5.end(),back_inserter(LIATE));
        }

        //coth
        if (!TCOH1.empty()) {
            copy(TCOH1.begin(),TCOH1.end(),back_inserter(LIATE));
        }
        if (!TCOH2.empty()) {
            copy(TCOH2.begin(),TCOH2.end(),back_inserter(LIATE));
        }
        if (!TCOH3.empty()) {
            copy(TCOH3.begin(),TCOH3.end(),back_inserter(LIATE));
        }
        if (!TCOH4.empty()) {
            copy(TCOH4.begin(),TCOH4.end(),back_inserter(LIATE));
        }
        if (!TCOH5.empty()) {
            copy(TCOH5.begin(),TCOH5.end(),back_inserter(LIATE));
        }

        return LIATE;

    }

    //partial integration by the formula: \int uv dx
    ex integratec::partial_integration(const ex& expr_, const bool &isFirstTime, const ex &partialIntegrandU,
                                       const ex &partialIntegrandV)
    {
        if(partial_num>0 && partial_num<partial_num_count)
            return Integrate(expr_,var,partial_num);
        //constant term integration//
        if (!expr_.has(var)) {
            return var*expr_;
        }

        //separating constant and variable dependent expression//
        ex constex=_ex1,varex=_ex1;
        if (is_a<mul>(expr_)) {
            //cout<<expr_<<endl;
            for(const_iterator itr=expr_.begin();itr!=expr_.end();++itr){
                if (!(*itr).has(var)) {
                    constex=constex*(*itr);
                }
                else {
                    varex=varex*(*itr);
                }
            }
        }
        else {
            varex=expr_;
        }

        const ex specialIntegration=do_inte(varex);
        if (!is_a<Integrate>(specialIntegration)){
            return (specialIntegration*constex);
        }

//        cout<<partial_num<<endl;
//        cout<<"partialIntegrandU*partialIntegrandV "<<partialIntegrandU*partialIntegrandV<<" "<<varex<<endl;
        if ((partialIntegrandU*partialIntegrandV).is_equal(varex)) {//terminating infinite integration by parts
            return Integrate(expr_,var,partial_num);;
        }

        if (!is_a<mul>(varex)) {//making mul container
            varex=externSymbols.symb_*varex;
        }


        exvector LIATE=Liate(varex,var);

        //        for(auto itr:LIATE) cout<<"jj "<<itr<<endl;

        //prtial integration//
        if (LIATE.size()==0){
            return constex*Integrate(varex,var,partial_num);
        }
        else if (LIATE.size()==1){
//            cout<<"LIATE[0]1 "<<func_inte(LIATE[0])<<endl;
            return constex*func_inte(LIATE[0],var,partial_num);
        }
        else if (LIATE.size()==2) {

            partial_num_count=partial_num_count+1;
            ex temintegrate=do_inte(expr_);//checking some special integral
            if (!is_a<Integrate>(temintegrate)) {
                return constex*temintegrate;
            }

            ex  integrationU=LIATE[0],
                integrationV=func_inte(LIATE[1],var,partial_num),
                integrationMag=integrationU*integrationV;
//                cout<<"integrationU "<<integrationU<<endl;
//                cout<<"integrationV "<<integrationV<<endl;

            if (is_a<Integrate>(integrationV)) {
                //cout<<"integrationV "<<integrationV<<endl;
                integrationV=do_inte(LIATE[1]);
                //cout<<"integrationV2 "<<integrationV<<endl;
                if (is_a<Integrate>(integrationV)) {
                    return Integrate(expr_,var,partial_num);
                }
            }

            //separating constant from integrationV//
            ex varex=_ex1;
            if (is_a<mul>(integrationV)){
                //cout<<expr_<<endl;
                for(const_iterator itr=integrationV.begin();itr!=integrationV.end();++itr){
                    if ((*itr).has(var)) {
                        varex=varex*(*itr);
                    }
                }
            }
            else {
                varex=integrationV;
            }

            if (!isFirstTime && (((integrationU/partialIntegrandU).is_equal(partialIntegrandU)||
                                  (varex/partialIntegrandV).is_equal(partialIntegrandV)||
                                 ((integrationU/partialIntegrandU).match(pow(partialIntegrandU,wild(1)))||
                                  (varex/partialIntegrandV).match(pow(partialIntegrandV,wild(1)))||
                                  (integrationU/partialIntegrandU).is_equal(_ex1)) ||
                                 (partial_num>0 && partial_num<partial_num_count))//||
                                 /*Simplify(varex/partialIntegrandV).is_equal(_ex1))*/)) {//terminating infinite integration by parts
                return Integrate(expr_,var,partial_num);
            }

            //cout<<"integrationMag2 "<<integrationMag<<endl;
            ex partialintterm=integrationU.diff(ex_to<symbol>(var))*(integrationV);
            ex tempartialintterm=(apart(partialintterm,ex_to<symbol>(var)));
            //cout<<"partialintterm "<<partialintterm<<endl;
            //cout<<"partialintterm2 "<<tempartialintterm<<endl;
            if (!is_a<fail>(tempartialintterm)) {
                partialintterm=expand(tempartialintterm);
            }
            else partialintterm=expand(partialintterm);
            ex temintegratesto=_ex0;
            //partial_num_count=partial_num_count+1;
            if(is_a<add>(partialintterm)){//integrate each add operand
                for(const_iterator itr=partialintterm.begin();itr!=partialintterm.end();itr++){
                    if(isFirstTime){
                        temintegratesto=temintegratesto+partial_integration(*itr,false,LIATE[0],LIATE[1]);
                    }
                    else
                        temintegratesto=temintegratesto+partial_integration(*itr,false,partialIntegrandU,partialIntegrandV);

                }
                integrationMag=integrationMag-temintegratesto;
            }
            else {
                if(isFirstTime)
                    integrationMag=integrationMag-
                                 partial_integration(partialintterm,false,LIATE[0],LIATE[1]);
                else
                    integrationMag=integrationMag-
                                     partial_integration(partialintterm,false,partialIntegrandU,partialIntegrandV);
            }


            return constex*integrationMag;
        }

        else /*if(LIATE.size()==3)*/ {
            if(partial_num>0 && partial_num<partial_num_count)
                return Integrate(expr_,var,partial_num);
            ex partiaSecondTerm;
            partial_num_count=partial_num_count+1;
            if(isFirstTime)
                partiaSecondTerm=expand(partial_integration(mul(exvector(LIATE.begin()+1,LIATE.end()))));
            else
                partiaSecondTerm=expand(partial_integration(mul(exvector(LIATE.begin()+1,LIATE.end())),
                                                           false,partialIntegrandU,partialIntegrandV));
//            cout<<"partiaSecondTerm "<<partiaSecondTerm<<endl;
            ex integratesto=_ex0;
            //partial_num_count=partial_num_count+1;
            if(is_a<add>(partiaSecondTerm)){//integrate each add operand
                for(const_iterator itr=partiaSecondTerm.begin();itr!=partiaSecondTerm.end();itr++){
                    if(isFirstTime)
                        integratesto=integratesto+constex*LIATE[0]*(*itr)
                                      -constex*partial_integration(LIATE[0].diff(ex_to<symbol>(var))*(*itr));
                    else integratesto=integratesto+constex*LIATE[0]*(*itr)
                                        -constex*partial_integration(LIATE[0].diff(ex_to<symbol>(var))*(*itr),
                                      false,partialIntegrandU,partialIntegrandV);
                }
                return integratesto;
            }
            else {
//                cout<<"LIATE[0] "<<LIATE[0]<<endl;
                if(isFirstTime)
                    return constex*LIATE[0]*(partiaSecondTerm)
                       -constex*partial_integration(LIATE[0].diff(ex_to<symbol>(var))*(partiaSecondTerm));
                else
                    return constex*LIATE[0]*(partiaSecondTerm)
                           -constex*partial_integration(LIATE[0].diff(ex_to<symbol>(var))*(partiaSecondTerm),
                                                 false,partialIntegrandU,partialIntegrandV);
            }

        }


        return Integrate(expr_,var,partial_num);
    }




    /** implementation of the class integratec **/
    /**************************************/

    ex integratec::operator()(const ex & expr_)
    {
        if(expr_ == _ex0)
            return expr_;
        ex expr, constterms;

        expr = expr_;
        expr = Simplify(expand(expr), simplify_options::TrigCombine);
        expr = Simplify(expand(expr), simplify_options::HyperCombine);
        //expr = Simplify(expand(expr), logSimp);
        //cout<<expr<<endl;
        expr=apart(expr,ex_to<symbol>(var));
        //cout<<expr<<endl;
        //expr = evaluate(expr);
        if (is_a<add>(expr))
        {
            exvector ev;
            for(size_t i=0;i<expr.nops();++i)
            {
                constterms = this->find_const(expr.op(i));
                if (expr.op(i).is_equal(constterms))
                    ev.push_back(expr.op(i)*this->var);
                else
                {
                    ev.push_back(Simplify((this->partial_integration(Simplify(expand(expr.op(i)/constterms)))*constterms)));
                }
            }
            ex tem = add(ev);
            return tem;
        }
        else
        {

            constterms = this->find_const(expr);

            if (expr.is_equal(constterms))
            {
                expr = expr*(this->var);
                return expr;
            }
            expr = Simplify(expand(expr/constterms));
            expr = this->partial_integration(expr);
            expr = expr*constterms;
            expr = Simplify(expand(expr));
            return expr;
        }
    }


    /** Integration of some functions **/
    /*************************************/
    ex func_inte(const ex& e, const ex& var, int partial_num)
    {
        /** functions **/
        if(is_a<functions>(e)){
            return Integrate(e,var,partial_num);
        }

        exmap repls;

        //collect var//
        ex expr_=collectAll(fullsimplify(e),var);


        /** polynomial **/
        if (expr_ == var)
            return _ex1_2*pow(var, 2);
        if ((1/expr_).is_polynomial(var) && (1/expr_).degree(var) == 1 )//1/(a*x+b)
            return log(1/expr_)/((1/expr_).coeff(var, 1));
        expr_.match(pow(var,wild(0)), repls);//x^n
        if (!repls.empty() && !repls[wild(0)].has(var))
            return pow(var, repls[wild(0)] + _ex1)/(repls[wild(0)] + _ex1);
        repls.clear();
        if (is_a<power>(expr_) && !expr_.op(1).has(var)//(a*x+b)^n
            && expr_.op(0).is_polynomial(var) && expr_.op(0).degree(var)==1) {
            return pow(expr_.op(0), expr_.op(1)+ _ex1)/(expr_.op(0).coeff(var)*(expr_.op(1) + _ex1));
        }


        /** rational functions **/
        repls.clear();
        expr_.match(1/(var+wild(0)), repls);//1/(a+x)
        if (!repls.empty() && !repls[wild(0)].has(var))
            return log(expr_);

        repls.clear();
        expr_.match(pow((var+wild(0)),wild(2)), repls);//1/(a+x)^n
        if (!repls.empty() && !repls[wild(0)].has(var)
            && repls[wild(2)].is_equal(_ex_1))
            return pow(expr_,repls[wild(2)]+1)/((repls[wild(2)]+1));

        repls.clear();
        expr_.match(pow((var*wild(1)+wild(0)),wild(2)), repls);//1/(a+b*x)^n
        if (!repls.empty() && !repls[wild(0)].has(var)
            && !repls[wild(1)].has(var)&& repls[wild(2)].is_equal(_ex_1))
            return pow(expr_,repls[wild(2)]+1)/(repls[wild(1)]*(repls[wild(2)]+1));

        repls.clear();
        expr_.match(pow((pow(var,2)+wild(0)),wild(2)), repls);//1/(a+x^2)
        if (!repls.empty() && !repls[wild(0)].has(var)
            && repls[wild(2)].is_equal(_ex_1))
            return atan(sqrt(1/repls[wild(0)])*var)/sqrt(repls[wild(0)]);

        repls.clear();
        expr_.match(pow((pow(var,2)*wild(1)+wild(0)),wild(2)), repls);//1/(a+b*x^2)
        if (!repls.empty() && !repls[wild(0)].has(var)
            && !repls[wild(1)].has(var)&& repls[wild(2)].is_equal(_ex_1))
            return atan(sqrt(repls[wild(1)]/repls[wild(0)])*var)/sqrt(repls[wild(1)]*repls[wild(0)]);

        repls.clear();
        expr_.match(pow((pow(var,2)+var+wild(0)),wild(2)), repls);//1/(a+x+x^2)
        if (!repls.empty() && !repls[wild(0)].has(var)
            && repls[wild(2)].is_equal(_ex_1))
            return 2*atan((2*var + 1)/sqrt(4*repls[wild(0)] - 1))/sqrt(4*repls[wild(0)] - 1);

        repls.clear();
        expr_.match(pow((pow(var,2)+wild(1)*var+wild(0)),wild(2)), repls);//1/(a+b*x+x^2)
        if (!repls.empty() && !repls[wild(0)].has(var) && !repls[wild(1)].has(var)
            && repls[wild(2)].is_equal(_ex_1))
            return -2*atanh((2*var + repls[wild(1)])/sqrt(pow(repls[wild(1)],2) - 4*repls[wild(0)]))/sqrt(pow(repls[wild(1)],2) - 4*repls[wild(0)]);

        repls.clear();
        expr_.match(pow((wild(1)*pow(var,2)+var+wild(0)),wild(2)), repls);//1/(a+x+b*x^2)
        if (!repls.empty() && !repls[wild(0)].has(var) && !repls[wild(1)].has(var)
            && repls[wild(2)].is_equal(_ex_1))
            return 2*atan((2*repls[wild(1)]*var + 1)/sqrt(4*repls[wild(0)]*repls[wild(1)] - 1))/sqrt(4*repls[wild(0)]*repls[wild(1)] - 1);

        repls.clear();
        expr_.match(pow((wild(2)*pow(var,2)+wild(1)*var+wild(0)),wild(3)), repls);//1/(a+b*x+c*x^2)
        if (!repls.empty() && !repls[wild(0)].has(var) && !repls[wild(1)].has(var)
            && !repls[wild(2)].has(var) && repls[wild(3)].is_equal(_ex_1))
            return ( var * pow(( repls[wild(0)] ),( -1 )) + ( _ex1_2 * pow(( var ),( 2 )) * repls[wild(1)] + 1/3 * pow(( var ),( 3 )) * repls[wild(2)] ) );


        repls.clear();
        expr_.match(pow((pow(var,2)+wild(0)),wild(2)), repls);//1/sqrt(a+x^2)
        if (!repls.empty() && !repls[wild(0)].has(var)
            && repls[wild(2)].is_equal(_ex_1_2))
            return (-_ex1_2*log((1+-1*var*pow(((pow((var),(2))+repls[wild(0)])),(-_ex1_2))))+_ex1_2*log((1+var*pow(((pow((var),(2))+repls[wild(0)])),(-_ex1_2)))));

        repls.clear();
        expr_.match(pow((pow(var,2)*wild(1)+wild(0)),wild(2)), repls);//1/sqrt(a+b*x^2)
        if (!repls.empty() && !repls[wild(0)].has(var)
            && !repls[wild(1)].has(var)&& repls[wild(2)].is_equal(_ex_1_2))
            return pow(( repls[wild(1)] ),( -_ex1_2 )) * atanh( var * pow(( repls[wild(1)] ),( _ex1_2 )) * pow(( ( repls[wild(0)] + pow(( var ),( 2 )) * repls[wild(1)] ) ),( -_ex1_2 )) );

        repls.clear();
        expr_.match(pow((pow(var,2)+var+wild(0)),wild(2)), repls);//1/sqrt(a+x+x^2)
        if (!repls.empty() && !repls[wild(0)].has(var)
            && repls[wild(2)].is_equal(_ex_1_2))
            return log( ( 1 + ( 2 * var + 2 * pow(( ( var + ( pow(( var ),( 2 )) + repls[wild(0)] ) ) ),( _ex1_2 )) ) ) );

        repls.clear();
        expr_.match(pow((pow(var,2)+wild(1)*var+wild(0)),wild(2)), repls);//1/sqrt(a+b*x+x^2)
        if (!repls.empty() && !repls[wild(0)].has(var) && !repls[wild(1)].has(var)
            && repls[wild(2)].is_equal(_ex_1_2))
            return log( ( 2 * var + ( repls[wild(1)] + 2 * pow(( ( pow(( var ),( 2 )) + ( repls[wild(0)] + var * repls[wild(1)] ) ) ),( _ex1_2 )) ) ) );

        repls.clear();
        expr_.match(pow((wild(1)*pow(var,2)+var+wild(0)),wild(2)), repls);//1/sqrt(a+x+b*x^2)
        if (!repls.empty() && !repls[wild(0)].has(var) && !repls[wild(1)].has(var)
            && repls[wild(2)].is_equal(_ex_1_2))
            return pow(( repls[wild(1)] ),( -_ex1_2 )) *log( ( 1 + ( 2 * var * repls[wild(1)] + 2 * pow(( repls[wild(1)] ),( _ex1_2 )) * pow(( ( var + ( repls[wild(0)] + pow(( var ),( 2 )) * repls[wild(1)] ) ) ),( _ex1_2 )) ) ) );

        repls.clear();
        expr_.match(pow((wild(2)*pow(var,2)+wild(1)*var+wild(0)),wild(3)), repls);//1/sqrt(a+b*x+c*x^2)
        if (!repls.empty() && !repls[wild(0)].has(var) && !repls[wild(1)].has(var)
            && !repls[wild(2)].has(var) && repls[wild(3)].is_equal(_ex_1_2)){
            return pow(( repls[wild(2)] ),( -_ex1_2 )) * log( ( repls[wild(1)] + ( 2 * var * repls[wild(2)] + 2 * pow(( repls[wild(2)] ),( _ex1_2 )) * pow(( ( repls[wild(0)] + ( var * repls[wild(1)] + pow(( var ),( 2 )) * repls[wild(2)] ) ) ),( _ex1_2 )) ) ) );
        }

        /** Exponential **/
        repls.clear();
        expr_.match(exp(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return expr_/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        /** logarithm **/
        expr_.match(log(wild(0)), repls);//log(a*x+b)
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return repls[wild(0)]*(log(repls[wild(0)]))/((repls[wild(0)]).coeff(var, 1))-var;

        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 2 )//log(a*x^2+b)
        {
            const ex a =  (repls[wild(0)]).coeff(var, 2), b  = (repls[wild(0)]).coeff(var, 1),
                c = (repls[wild(0)]).coeff(var, 0);
            //if ((4*a_*c_ - pow(b_,2)) > _ex0 )
            return _ex1_2 * pow(( a ),( -1 )) * ( -4 * a * var + ( 2 * pow(( ( pow(( b ),( 2 )) + -4 * a * c ) ),( _ex1_2 )) * atanh( pow(( ( pow(( b ),( 2 )) + -4 * a * c ) ),( -_ex1_2 )) * ( b + 2 * a * var ) ) + ( b + 2 * a * var ) * log( ( c + var * ( b + a * var ) ) ) ) );
        }

        repls.clear();
        if(expr_.match(log(wild(1)*pow(var,wild(0))), repls)
            && !repls.empty() && !repls[wild(1)].has(var) && !repls[wild(0)].has(var))//log(a*x^n)
        {
            const ex a =  (repls[wild(1)]),b =  (repls[wild(0)]);
            return ( -1 * b * var + var * log( a * pow(( var ),( b )) ) );
        }

        repls.clear();
        /** Derivative **/
        expr_.match(Diff(wild(0), wild(1), wild(2)), repls);
        if (!repls.empty())
        {
            if (repls[wild(2)] > _ex0 && repls[wild(1)] == var)
                return Diff(repls[wild(0)], repls[wild(1)], repls[wild(2)] - 1);
            else
                return Integrate(expr_, var,partial_num);
        }

        repls.clear();
        /** Integrate **/
        expr_.match(Integrate(wild(0), var), repls);
        if (!repls.empty())
            return Integrate(expr_, var,partial_num);

        repls.clear();
        /** trigonometric functions **/
        expr_.match(sin(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return -cos(repls[wild(0)])/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        expr_.match(cos(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return sin(repls[wild(0)])/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        expr_.match(tan(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return  _ex1_2*log(pow(tan(repls[wild(0)]), 2) + _ex1)/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        expr_.match(csc(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return  log(tan(_ex1_2*repls[wild(0)]))/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        expr_.match(sec(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return  ( log(tan(_ex1_2*(repls[wild(0)])) + _ex1) - log(tan(_ex1_2*(repls[wild(0)])) + _ex_1))/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        expr_.match(cot(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return  (log(tan(_ex1_2*(repls[wild(0)]))) - log(pow(tan(_ex1_2*(repls[wild(0)])), 2) + _ex1))/((repls[wild(0)]).coeff(var, 1));

        /** Hyperbolic functions sinh, cosh, tanh **/
        repls.clear();
        expr_.match(sinh(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return cosh(repls[wild(0)])/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        expr_.match(cosh(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return sinh(repls[wild(0)])/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        expr_.match(tanh(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return log(cosh(repls[wild(0)]))/((repls[wild(0)]).coeff(var, 1));

        /** some algebraic functions **/

        /** asin, acos, atan, acsc, asec, acot **/
        repls.clear();
        expr_.match(asin(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return repls[wild(0)]*asin(repls[wild(0)])/(repls[wild(0)]).coeff(var, 1) + sqrt(-pow(repls[wild(0)],2) + _ex1)/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        expr_.match(acos(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return repls[wild(0)]*asin(repls[wild(0)])/(repls[wild(0)]).coeff(var, 1) + sqrt(-pow(repls[wild(0)],2) + _ex1)/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        expr_.match(atan(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return repls[wild(0)]*atan(repls[wild(0)])/(repls[wild(0)]).coeff(var, 1)+(_ex_1_2)*log(pow(repls[wild(0)],2)+_ex1)/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        expr_.match(acsc(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return acsc(repls[wild(0)])*repls[wild(0)]/(repls[wild(0)]).coeff(var, 1)+log(repls[wild(0)]+repls[wild(0)]*sqrt(_ex1+_ex_1/pow(repls[wild(0)],2)))/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        expr_.match(asec(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return asec(repls[wild(0)])*repls[wild(0)]/(repls[wild(0)]).coeff(var, 1)-log(repls[wild(0)]+repls[wild(0)]*sqrt(_ex1+_ex_1/pow(repls[wild(0)],2)))/((repls[wild(0)]).coeff(var, 1));

        repls.clear();
        expr_.match(acot(wild(0)), repls);
        if (!repls.empty() && (repls[wild(0)]).is_polynomial(var) && (repls[wild(0)]).degree(var) == 1 )
            return acot(repls[wild(0)])*repls[wild(0)]/(repls[wild(0)]).coeff(var, 1)+(_ex1_2)*log(pow(repls[wild(0)],2)+_ex1)/((repls[wild(0)]).coeff(var, 1));


        return Integrate(expr_, var,partial_num);
    }
}

/////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////























