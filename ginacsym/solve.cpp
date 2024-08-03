
/** @file solve.cpp
 *
 *  Solving a system of linear or nonlinear polynomial equations (implementation). **/

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

#include <bits/stdc++.h>
#include "constant.h"
#include "ex.h"
#include "factor.h"
#include "ginacwrapper.h"
#include "infinity.h"
#include "normal.h"
#include "simplify.h"
#include "utility.h"
#include "solve.h"
#include "inifcns.h"
#include "add.h"
#include "mul.h"
#include "power.h"
#include<cln/exception.h>


namespace ginacsym{
/** counting total number of add in an equation**/
ex totalAddInEq::expr_visitor(const ex &_e)
{
    if(is_a<add>(_e))
        addNum=addNum+(nops(_e)-1);
    return _e.map(*this);
}

/** replacing the "pow" terms where present _var with created symbols **/
ex powBaseSubsWtVar::expr_visitor(const ex& _e)
{
    if(exprToSymMapWtVar.size()>1)
        return _e;

    else if(is_a<power>(_e)&&(_e.op(0).has(_var))) // substituting power which have _var
    {
        if((!exprToSymMapWtVar.empty() && exprToSymMapWtVar.find(_e)==exprToSymMapWtVar.end())
            ||exprToSymMapWtVar.empty())
        {
            j=j+1;

            str = "powBaseSubsWtVar_" + to_string(j);
            expr = generator.symGenerator(str);
            exprToSymMapWtVar[_e]=expr;
        }
        if(!exprToSymMapWtVar.empty() && exprToSymMapWtVar.find(_e)!=exprToSymMapWtVar.end())
            return exprToSymMapWtVar[_e];
    }

    return _e.map(*this);
};

/** replacing the "pow" terms without _var with created symbols. **/
ex powBaseSubsWtoutVar::expr_visitor(const ex& _e)
{
    if(is_a<power>(_e)&&!(_e.op(0).has(_var))) // substituting power which does not have _var
    {
        if((!exprToSymMapWtoutVar.empty() && exprToSymMapWtoutVar.find(_e)==exprToSymMapWtoutVar.end())
            ||exprToSymMapWtoutVar.empty())
        {
            j=j+1;

            str = "powBaseSubsWtout_" + to_string(j);
            expr = generator.symGenerator(str);
            exprToSymMapWtoutVar[_e]=expr;
        }
        if(!exprToSymMapWtoutVar.empty() && exprToSymMapWtoutVar.find(_e)!=exprToSymMapWtoutVar.end())
            return exprToSymMapWtoutVar[_e];
    }

    return _e.map(*this);
};

/** Square root of complex numbers. **/
ex solvec::sqroot(const ex& _exp)
{
    if(!is_a<numeric>(_exp))
        return _ex_1;
    if(_exp.info(info_flags::real))
        return sqrt(_exp);
    else
    {
        ex re, im;
        re = real_part(evalf(_exp));
        im = imag_part(evalf(_exp));
        ex tem = evalf(sqrt(_ex1_2*(sqrt(re*re+im*im) - re)));
        return evalf(_ex1_2*im/tem) + sqrt(_ex_1)*tem;
    }
}


/** Solutions of linear and quadratic polynomial equation **/
lst solvec::quadratic(const ex & equ_, const ex& var_)
{
    lst quasolu;

    if(equ_.degree(var_) == 0)
        return quasolu;

    if(equ_.degree(var_) == 1)
        quasolu.append(var_ == simplify(Simplify(_ex_1*equ_.coeff(var_, 0)))/(Simplify(equ_.coeff(var_, 1))));
    else
     {
         ex _a, _b, _c;

        _a = Simplify(equ_.coeff(var_, 2));
        _b = Simplify(equ_.coeff(var_, 1));
        _c = Simplify(equ_.coeff(var_, 0));

        if(_b.is_zero()&&_c.is_zero())
            return lst{var_==_ex0};

        ex tem = Simplify(_b*_b - 4*_a*_c);
        if(tem == _ex0)
        {
            quasolu.append(var_ == simplify((_ex1_2*(-_b))/_a));
        }
        else
        {
            quasolu.append(var_ == simplify(Simplify(_ex1_2*(-_b + sqrt(tem)))/_a));
            quasolu.append(var_ == simplify(Simplify(_ex1_2*(-_b - sqrt(tem)))/_a));
        }
     }

    for(unsigned i = 0; i < nops(quasolu); i++)
    {
        if(quasolu.op(i).rhs().info(info_flags::positive) && quasolu.op(i).rhs() < Gtolerance)
            quasolu[i] = {var_ == _ex0};
        else if(quasolu.op(i).rhs().info(info_flags::negative) && -quasolu.op(i).rhs() < Gtolerance)
            quasolu[i] = {var_ == _ex0};
    }

    return quasolu;
}

/** algebraic solutions of cubic polynomial equation by cardan's method **/
lst solvec::cubics(const ex & equ_, const ex & var_)
{
    lst cubicsolu;
    try
    {
        ex equ=expand(equ_);
// Define the coefficients of the cubic equation ax^3+bx^2+cx+d
        const ex a = Simplify(equ.coeff(var_, 3)),
                b = Simplify((equ.coeff(var_, 2))),
                c = Simplify((equ.coeff(var_, 1))),
                d = Simplify((equ.coeff(var_, 0)));

        if(b.is_zero()&&c.is_zero()&&d.is_zero())
            return lst{var_==_ex0};
// formula has been taken from maplesoft software
        cubicsolu.append(var_== Simplify(pow((12*sqrt(_ex3)*sqrt(27*pow(a,2)*pow(d,2) - 18*a*b*c*d + 4*a*pow(c,3) + 4*pow(b,3)*d - pow(b,2)*pow(c,2))*a - 108*d*pow(a,2) + 36*c*b*a - 8*pow(b,3)),(_ex1/3))/(6*a) - 2*(3*a*c - pow(b,2))/(3*a*pow((12*sqrt(_ex3)*sqrt(27*pow(a,2)*pow(d,2) - 18*a*b*c*d + 4*a*pow(c,3) + 4*pow(b,3)*d - pow(b,2)*pow(c,2))*a - 108*d*pow(a,2) + 36*c*b*a - 8*pow(b,3)),(_ex1/3))) - b/(3*a) ));
        cubicsolu.append(var_== Simplify(-pow((12*sqrt(_ex3)*sqrt(27*pow(a,2)*pow(d,2) - 18*a*b*c*d + 4*a*pow(c,3) + 4*pow(b,3)*d - pow(b,2)*pow(c,2))*a - 108*d*pow(a,2) + 36*c*b*a - 8*pow(b,3)),(_ex1/3))/(12*a) + (3*a*c - pow(b,2))/(3*a*pow((12*sqrt(_ex3)*sqrt(27*pow(a,2)*pow(d,2) - 18*a*b*c*d + 4*a*pow(c,3) + 4*pow(b,3)*d - pow(b,2)*pow(c,2))*a - 108*d*pow(a,2) + 36*c*b*a - 8*pow(b,3)),(_ex1/3))) - b/(3*a) + sqrt(_ex3)*(pow((12*sqrt(_ex3)*sqrt(27*pow(a,2)*pow(d,2) - 18*a*b*c*d + 4*a*pow(c,3) + 4*pow(b,3)*d - pow(b,2)*pow(c,2))*a - 108*d*pow(a,2) + 36*c*b*a - 8*pow(b,3)),(_ex1/3))/(6*a) + 2*(3*a*c - pow(b,2))/(3*a*pow((12*sqrt(_ex3)*sqrt(27*pow(a,2)*pow(d,2) - 18*a*b*c*d + 4*a*pow(c,3) + 4*pow(b,3)*d - pow(b,2)*pow(c,2))*a - 108*d*pow(a,2) + 36*c*b*a - 8*pow(b,3)),(_ex1/3))))*I/2));
        cubicsolu.append(var_== Simplify(-pow((12*sqrt(_ex3)*sqrt(27*pow(a,2)*pow(d,2) - 18*a*b*c*d + 4*a*pow(c,3) + 4*pow(b,3)*d - pow(b,2)*pow(c,2))*a - 108*d*pow(a,2) + 36*c*b*a - 8*pow(b,3)),(_ex1/3))/(12*a) + (3*a*c - pow(b,2))/(3*a*pow((12*sqrt(_ex3)*sqrt(27*pow(a,2)*pow(d,2) - 18*a*b*c*d + 4*a*pow(c,3) + 4*pow(b,3)*d - pow(b,2)*pow(c,2))*a - 108*d*pow(a,2) + 36*c*b*a - 8*pow(b,3)),(_ex1/3))) - b/(3*a) - sqrt(_ex3)*(pow((12*sqrt(_ex3)*sqrt(27*pow(a,2)*pow(d,2) - 18*a*b*c*d + 4*a*pow(c,3) + 4*pow(b,3)*d - pow(b,2)*pow(c,2))*a - 108*d*pow(a,2) + 36*c*b*a - 8*pow(b,3)),(_ex1/3))/(6*a) + 2*(3*a*c - pow(b,2))/(3*a*pow((12*sqrt(_ex3)*sqrt(27*pow(a,2)*pow(d,2) - 18*a*b*c*d + 4*a*pow(c,3) + 4*pow(b,3)*d - pow(b,2)*pow(c,2))*a - 108*d*pow(a,2) + 36*c*b*a - 8*pow(b,3)),(_ex1/3))))*I/2));
        //// calculate intermediate values
//        const ex  p = (3*a*c - pow(b,2)) / (3*pow(a,2)),
//                  q = (2*pow(b,3) - 9*a*b*c + 27*pow(a,2)*d) / (27*pow(a,3)),
//                  delta = (pow(q,2) / 4 + pow(p,3) / 27);

//// determine number and type of roots
////        if (delta > 0){  // one real and two complex roots
//            const ex    u = pow((-q/2 + sqrt(delta)),(_ex1/3)),
//                        v = pow((-q/2 - sqrt(delta)),(_ex1/3));
//            cubicsolu.append(var_== Simplify( u + v - b / (3*a)));
//            cubicsolu.append(var_== Simplify( -(u + v)/2 - b / (3*a) + (u - v)*sqrt(_ex3)/2*I));
//            cubicsolu.append(var_== Simplify(-(u + v)/2 - b / (3*a) - (u - v)*sqrt(_ex3)/2*I));
//            return cubicsolu;
//        //}
///*        else */if (delta.is_equal(_ex0)){  //three real roots, two are equal
//             const ex   u = pow((-q/2),(_ex1/3)),
//                        v = u;
//            cubicsolu.append(var_== Simplify(2*u - b / (3*a)));
//            cubicsolu.append(var_== Simplify(-u - b / (3*a)));

//                                                        }
//        else{  // three distinct real roots
//            const ex    u = pow((-q/2 + sqrt(delta)),(_ex1/3)),
//                        v = pow((-q/2 - sqrt(delta)),(_ex1/3));
//                        cubicsolu.append(var_== ( (u + v - b / (3*a)).real_part()));
//                        cubicsolu.append(var_== Simplify(( -(u + v)/2 - b / (3*a) + (u - v)*sqrt(_ex3)/2*I)).real_part());
//                        cubicsolu.append(var_== Simplify((-(u + v)/2 - b / (3*a) - (u - v)*sqrt(_ex3)/2*I)).real_part());

//            return cubicsolu;
//        }
    }
    catch(cln::runtime_exception){return cubicsolu;}


    return cubicsolu;
}
/**Numerical solutions of cubic polynomial equation **/
lst solvec::Ncubics(const ex & equ_, const ex& var_)
{
    lst cubicsolu;

    const ex _p = equ_.coeff(var_, 3),
            p = Simplify(equ_.coeff(var_, 2)/_p),
            q = Simplify(equ_.coeff(var_, 1)/_p),
            r = Simplify(equ_.coeff(var_, 0)/_p);

    if(!_p.info(info_flags::numeric) || !p.info(info_flags::numeric) || !q.info(info_flags::numeric)
       || !r.info(info_flags::numeric) )
      {
          return {};
      }

    const ex _ex1_27 = (ex)1/27, _ex1_3 = (ex)1/3;

    const ex a = Simplify(_ex1_3*(3*q - p*p)),
             b = Simplify(_ex1_27*(2*p*p*p - 9*p*q + 27*r));

    ex discriminant = Simplify(_ex1_4*b*b + _ex1_27*a*a*a);
    if(is_a<numeric>(b) && is_a<numeric>(discriminant))
    {
        if(discriminant == _ex0)
        {
            if(b > _ex0)
            {
                cubicsolu.append(var_ == -2*sqrt(-_ex1_3*a) - _ex1_3*p );
                cubicsolu.append(var_ == sqrt(-_ex1_3*a) - _ex1_3*p );
                cubicsolu.append(var_ == sqrt(-_ex1_3*a) - _ex1_3*p );
            }
            else if(b < _ex0)
            {
                cubicsolu.append(var_ == 2*sqrt(-_ex1_3*a) - _ex1_3*p );
                cubicsolu.append(var_ == -sqrt(-_ex1_3*a) - _ex1_3*p );
                cubicsolu.append(var_ == -sqrt(-_ex1_3*a) - _ex1_3*p );
            }
            else
            {
                cubicsolu.append(var_ == _ex0 - _ex1_3*p );
                cubicsolu.append(var_ == _ex0 - _ex1_3*p );
                cubicsolu.append(var_ == _ex0 - _ex1_3*p );
            }
        }

        else if(discriminant < _ex0)
        {
            ex phi;

            if(b >= _ex0)
            {
               phi = acos(-sqrt(_ex_1_4*(27*b*b)/(a*a*a)));
               if(is_ex_the_function(phi, acos))
                    phi = acos(evalf(-sqrt(_ex_1_4*(27*b*b)/(a*a*a))));
            }
            else
            {
                phi = acos(sqrt(_ex_1_4*(27*b*b)/(a*a*a)));
               if(is_ex_the_function(phi, acos))
                    phi = acos(evalf(sqrt(_ex_1_4*(27*b*b)/(a*a*a))));
            }

            ex tem = cos(_ex1_3*phi);
            if(is_ex_the_function(tem, cos))
                tem = cos(evalf(_ex1_3*phi));

            cubicsolu.append(var_ == evalf(Simplify(-_ex1_3*p + 2*sqrt(-_ex1_3*a)*(tem))));

            tem = cos(_ex1_3*phi + 2*_ex1_3*(Pi));
            if(is_ex_the_function(tem, cos))
                tem = cos(evalf(_ex1_3*phi + 2*_ex1_3*(Pi)));
            cubicsolu.append(var_ == evalf(Simplify(-_ex1_3*p + 2*sqrt(-_ex1_3*a)*(tem))));

            tem = cos(_ex1_3*phi + 4*_ex1_3*(Pi));
            if(is_ex_the_function(tem, cos))
                tem = cos(evalf(_ex1_3*phi + 4*_ex1_3*(Pi)));
            cubicsolu.append(var_ == evalf(Simplify(-_ex1_3*p + 2*sqrt(-_ex1_3*a)*(tem))));

        }

        else
        {
            ex A, B, tem;

            tem = evalf(Simplify(_ex_1_2*b + sqrt(discriminant)));
            if(tem.info(info_flags::negative))
                A = -evalf(pow((-tem), _ex1_3));
            else
                A = evalf(pow((tem), _ex1_3));
            tem = evalf(Simplify(_ex_1_2*b - sqrt(discriminant)));

            if(tem.info(info_flags::negative))
                B = -evalf(pow((-tem), _ex1_3));
            else
                B = evalf(pow((tem), _ex1_3));

            ex three = 3;
            cubicsolu.append(var_ == evalf(Simplify(A + B - _ex1_3*p)));
            cubicsolu.append(var_ == evalf(Simplify(_ex_1_2*(A + B) + sqrt(_ex_1)*_ex1_2*sqrt(three)*(A - B) - _ex1_3*p)));
            cubicsolu.append(var_ == evalf(Simplify(_ex_1_2*(A + B) - sqrt(_ex_1)*_ex1_2*sqrt(three)*(A - B) - _ex1_3*p)));
        }
    }

    for(unsigned i = 0; i < nops(cubicsolu); i++)
    {
        if(cubicsolu.op(i).rhs().info(info_flags::positive) && cubicsolu.op(i).rhs() < ginacsym::pow(10, -10))
            cubicsolu[i] = {var_ == _ex0};
        else if(cubicsolu.op(i).rhs().info(info_flags::negative) && -cubicsolu.op(i).rhs() < ginacsym::pow(10, -10))
            cubicsolu[i] = {var_ == _ex0};
    }

    return cubicsolu;

}

/**Numerical solutions of quartic polynomial equation (Euler's solution) **/
lst solvec::Nquartic(const ex & equ_, const ex& var_)
{
    lst quarticsolu;

    const ex a = equ_.coeff(var_, 4),
            b = equ_.coeff(var_, 3)/a,
            c = equ_.coeff(var_, 2)/a,
            d = equ_.coeff(var_, 1)/a,
            e = equ_.coeff(var_, 0)/a;

    if(!a.info(info_flags::numeric) || !b.info(info_flags::numeric) || !c.info(info_flags::numeric)
       || !d.info(info_flags::numeric) || !e.info(info_flags::numeric) )
        {
            return {};
        }

    if(b.is_zero()&&c.is_zero()&&d.is_zero()&&e.is_zero())
        return lst{var_==_ex0};

    const ex _ex1_8 = (ex)1/8, _ex1_256 = (ex)1/256, _ex1_16 = (ex)1/16, _ex1_64 = (ex)1/64;

    const ex f = Simplify(c - (3*b*b*_ex1_8)),
            g = Simplify(d + (_ex1_8*b*b*b) - (_ex1_2*b*c)),
            h = Simplify((e) - 3*_ex1_256*pow(b,4) +(_ex1_16*b*b*c) - (_ex1_4*b*d));

    const lst cubicsolu = this->Ncubics(pow(var_, 3) + (_ex1_2*f)*var_*var_ + Simplify(_ex1_16*(f*f - 4*h))*var_ -_ex1_64*g*g, var_);

    if(nops(cubicsolu) == _ex0)
        return quarticsolu;

    lst sqrtli;

    for(auto it =cubicsolu.begin(); it != cubicsolu.end(); it++)
    {
        if(!((*it).info(info_flags::real)))
            sqrtli.append(this->sqroot(*it));
    }
    if(nops(sqrtli) < 2)
    {
       for(auto it = cubicsolu.begin(); it != cubicsolu.end(); it++)
       {
        if((*it) != _ex0)
            sqrtli.append(this->sqroot(*it));
        }
    }

    if(nops(sqrtli) < 2)
     return quarticsolu;

    const ex p = sqrtli.op(0),
            q = sqrtli.op(1),
            r = Simplify(-_ex1_8*g/(p*q)),
            s = Simplify(_ex1_4*b);

    quarticsolu.append(var_ == evalf(Simplify(p + q + r -s)));
    quarticsolu.append(var_ == evalf(Simplify(p - q - r -s)));
    quarticsolu.append(var_ == evalf(Simplify(-p + q - r - s)));
    quarticsolu.append(var_ == evalf(Simplify(-p - q + r - s)));

    for(unsigned i = 0; i < nops(quarticsolu); i++)
    {
        if(quarticsolu.op(i).rhs().info(info_flags::positive) && quarticsolu.op(i).rhs() < Gtolerance
            || quarticsolu.op(i).rhs().info(info_flags::negative) && -quarticsolu.op(i).rhs() < Gtolerance)
            quarticsolu[i] = {var_ == _ex0};
    }

    return quarticsolu;

}

// solution of x in equation x^n=c using the following formulae//
//        x^n=-1, n is even
//        x= -(-1)^1/n, (-1)^1/n, -(-1)^3/n,  (-1)^3/n,....... -(-1)^(n-1)/n, (-1)^(n-1)/n.
//        x^n=-1, n is odd
//        x= (-1)^1/n, -(-1)^2/n, (-1)^3/n, - (-1)^4/n,....... -(-1)^(n-1)/n, (-1)^n/n.

//        x^n=1, n is even
//        x= -(-1)^2/n, (-1)^2/n, -(-1)^4/n,  (-1)^4/n,....... -(-1)^n/n, (-1)^n/n.
//        x^n=1, n is odd
//        x= -(-1)^1/n, (-1)^2/n, -(-1)^3/n,  (-1)^4/n,....... (-1)^(n-1)/n, -(-1)^n/n.
//
//        If c is integer (positive or negative) then c=1*c and only positive case is considered.
//        If c is symbol positive case is considered.
//        In other cases, for positive, positive and for negative, negative case is considered.
//        Ex:x^n=5=1*5, x^n=-5=1*-5, x^n=c=1*c,
//             x^n=√2=1*√2, x^n=-√2=-1*√2,
//             x^n=a^2=1*a^2, x^n=-a^2=-1*a^2
lst xnc(const ex& x, const ex& n, const ex& c)
{
//    cout<<"x "<<x<<" n "<<n<<endl;
    lst solulst;
    if(!(c).info(info_flags::integer) &&((c).info(info_flags::negative)||
      (!is_a<symbol>(c)&&is_a<mul>(c) &&(c).op((c).nops()-1).info(info_flags::negative)))){//negative case

        if(n.info(info_flags::even)){
            for (int i = 1; i <= n/2; ++i) {
                solulst.append(x==pow((-c),_ex1/n)*(_ex_1*pow(_ex_1,(2*i-1)/n)));
                solulst.append(x==pow((-c),_ex1/n)*(_ex1*pow(_ex_1,((2*i-1))/n)));
            }
        }
        else{//odd case
            for (int i = 1; i <= n; ++i) {
                solulst.append(x==pow((-c),_ex1/n)*(pow(_ex_1,i+1)*pow(_ex_1,i/n)));
            }

        }
    }
    else{//positive case
        if(n.info(info_flags::even)){
            for (int i = 1; i <= n/2; ++i) {
                solulst.append(x==pow((c),_ex1/n)*(_ex_1*pow(_ex_1,2*i/n)));
                solulst.append(x==pow((c),_ex1/n)*(_ex1*pow(_ex_1,2*i/n)));
            }
        }
        else{//odd case
            for (int i = 1; i <= n; ++i) {
                solulst.append(x==pow((c),_ex1/n)*(pow(_ex_1,i)*pow(_ex_1,i/n)));
            }

        }
    }
    return solulst;
}

/// solu1 solutions are substituted by solu2 solutions
lst soluSubs(const lst& solu1, const lst& solu2)
{
    lst tem;
    ex xprev, xnow;
    bool den_zero;


    for(lst::const_iterator it = solu2.begin(); it != solu2.end(); it++)
    {
        den_zero = false;
        for(lst::const_iterator it1 = solu1.begin(); it1 != solu1.end(); it1++){
            xnow = (*it1).rhs();

            den_zero = false;
            do
            {
                xprev = (xnow);
                try
                {
                    xnow = Simplify((xprev)).subs((*it), subs_options::algebraic);
                    if (xnow.has(Infinity) || xnow.has(-Infinity)) {
                        den_zero=false;
                    }
                }
                catch(ginacsym::pole_error){den_zero = true;}
                catch(ginacsym::indeterminate_error){den_zero = true;}

            } while(xprev != xnow && den_zero == false);
            if(den_zero == false)
                tem.append(((*it1)).lhs() == xnow);
        }
    }

    return tem;
}


//callback function for sorting a and b according to their number of add operand.
bool addcmp(const ex& a, const ex& b)
{
//    if(is_a<power>(a) && is_a<power>(b))
//        return nops(a.op(0))<nops(b.op(0));
//    else if(is_a<power>(a))
//        return nops(a.op(0))<nops(b);
//    else if(is_a<power>(b))
//        return nops(a)<nops(b.op(0));
//    else
        return nops(a)<nops(b);
}

/** solution of single polynomial equation **/
lst solvec::polySolve(const ex& _equ, const ex& _var, unsigned int tryno)
{
//    cout<<"_equ "<<_equ<<endl;
    if(!_equ.is_polynomial(_var)){
        soluCltPoly={};
        return {};
    }

    ex allterms=collect(expand(_equ),_var);

        lst solulst;
        exmap temmap;
        if((allterms).degree(_var) < 3 && allterms.degree(_var) > 0) // linear and quadratic equation
        {
            solulst = this->quadratic((allterms), _var);

            if(nops(solulst)!=0){
                if(nops(soluCltPoly)!=0){
                    /// solulst solutions are substituted by soluCltPoly solutions
                    soluCltPoly=soluSubs(solulst,soluCltPoly);
                    return solulst;
                }
                else{
                    soluCltPoly=solulst;
                    return solulst;
                }
            }
        }
//        else if((_equ).degree(_var) == 3) // cubic equation
//        {
//            solulst = this->cubics((allterms), _var);

//            if(nops(solulst)!=0){
//                if(nops(soluCltPoly)!=0){
//                    /// solulst solutions are substituted by soluCltPoly solutions
//                    soluCltPoly=soluSubs(solulst,soluCltPoly);
//                    return solulst;
//                }
//                else{
//                    soluCltPoly=solulst;
//                    return solulst;
//                }
//            }
//        }
//        else if((_equ).degree(_var) == 4) // quartic equation
//        {
//            solulst = this->Nquartic((_equ), _var);

//            if(nops(solulst)!=0){
//                if(nops(soluCltPoly)!=0){
//                    /// solulst solutions are substituted by soluCltPoly solutions
//                    soluCltPoly=soluSubs(solulst,soluCltPoly);
//                    return solulst;
//                }
//                else{
//                    soluCltPoly=solulst;
//                    return solulst;
//                }
//            }
//        }
        else if((allterms).match(pow(wild(0),wild(1))+wild(2),temmap) &&
                   temmap[wild(0)]==_var &&
                   temmap[wild(1)].info(info_flags::integer) &&
                   !temmap[wild(2)].has(_var)){ //solve x^n=c,n>3
            solulst= xnc(temmap[wild(0)],temmap[wild(1)],-temmap[wild(2)]);
            if(nops(solulst)!=0){
                if(nops(soluCltPoly)!=0){
                    /// solulst solutions are substituted by soluCltPoly solutions
                    soluCltPoly=soluSubs(solulst,soluCltPoly);
                    return solulst;
                }
                else{
                    soluCltPoly=solulst;
                    return solulst;
                }
            }
        }


        if(tryno==1){
            ///If allterms can be expressed in such form that some combination of terms in allterms can be factored,
            /// and the factored terms has similar forms (Ex.f((x+4)*(x+2))= (x+4)^4*(x+2)^2+(x+4)^2*(x+2)+8),
            /// then if we differentiate allterms w.r.t. _var, minimum one factored terms is obtained
            /// (Ex. (x+4)*f'((x+4)*(x+2)).///
            /// These factored terms are collected in factclt.
            const ex factored=factor(allterms.diff(ex_to<symbol>(_var)));
            if(!is_a<mul>(factored)) return polySolve(allterms,_var,2);//second try to solve the equations like: x^4+x^2+c=0
            vector<ex> factclt;
            for(const_iterator itr=factored.begin();itr!=factored.end();++itr){
                if((*itr).has(_var)){
                    if (is_a<power>(*itr))
                        factclt.push_back((*itr).op(0));
                    else factclt.push_back((*itr));
                }
            }
            if (factclt.empty()) {
                return polySolve(allterms,_var,2);//second try to solve the equations like: x^4+x^2+c=0
            }
            sort(factclt.begin(),factclt.end(),addcmp);//sorting factors with asecending order of add operands
//            for(auto it:factclt)
//                cout<<"facclt"<<it<<endl;


            exset factortermclt,factortermset;
            ex  temfactorterm,temfactortermsto,constantfactor,
                remexpr,quoexprfactor,
                temallterms,
                remfactor2=_ex0;
            size_t deg=degree(allterms,_var),degnow;
            lst solucheck={},//It is used to check whether the factors in factclt can solve the _equ
                powTermClt={};//collector of degree of each term in temfactorterm

            for(auto it=factclt.begin();it!=factclt.end();it++){ // The correct factor from factclt is selected///////
                if(nops(solucheck)!=0)
                    break;

                temfactorterm=*it;
                temallterms=allterms;
                bool iswhileloopbreak=false;
                while(!temallterms.is_equal(_ex0)){

                    ///temallterms is divided by *it to determine remainder and quotient
                    remexpr=rem(temallterms,*it,_var);
//                    cout<<"facc "<<*it<<endl;
//                    cout<<"remexpr "<<remexpr<<endl;
                    if(remexpr.has(_var)){
                        break;//break while loop
                    }
                    quoexprfactor=factor(quo(temallterms,*it,_var));
//                    cout<<"quoexprfactor "<<quoexprfactor<<endl;


                    ///it is checked that whether temallterms is reached to last factored term
                    /// and if it reaches to last factored term then while loop is breaked.
                    if(factortermclt.size()>1){
                        ex quoexprfactormulit=quoexprfactor*(*it);
                        ex temquoexprfactormulit=_ex1;
                        constantfactor=_ex1;
                        //isolating constant factor
                        for(const_iterator itr=quoexprfactormulit.begin();itr!=quoexprfactormulit.end();++itr){
//                            cout<<"uiop "<<*itr<<endl;
                            if ((*itr).has(_var)) {
                                temquoexprfactormulit=temquoexprfactormulit*(*itr);
                            }
                            else constantfactor=constantfactor*(*itr);
                        }

                        ///GCD of the powers of each factor terms is calculated
                        ///  and their powers are multiplied with 1/GCD
                        temfactortermsto=_ex1;
                        if(is_a<mul>(temquoexprfactormulit) && temquoexprfactormulit.has(_var)){
                            powTermClt.remove_all();
                            for(const_iterator itr=temquoexprfactormulit.begin();itr!=temquoexprfactormulit.end();++itr){
                                if (is_a<power>(*itr) && (*itr).has(_var)) {
                                    powTermClt.append((*itr).op(1));
                                }
                                else if ((*itr).has(_var)) powTermClt.append(1);
                            }
                            ex GCD =Gcd(powTermClt);
                            if(!GCD.is_equal(_ex1)){
                                for(const_iterator itr=temquoexprfactormulit.begin();itr!=temquoexprfactormulit.end();++itr){//simplify (z^a)^1/GCD=x^(a/GCD)
                                    if (is_a<power>(*itr) && (*itr).has(_var)) {
                                        temfactortermsto=temfactortermsto*pow((*itr).op(0), (*itr).op(1)*1/GCD);
                                    }
                                    else{
                                        temfactortermsto=temfactortermsto*(*itr);
                                    }
                                }
                            }
                            else {
                                temfactortermsto=temquoexprfactormulit;
                            }
                        }
                        else {
                            if (is_a<power>(temquoexprfactormulit)) {
                                temfactortermsto=temquoexprfactormulit.op(0);
                            }
                            else temfactortermsto=temquoexprfactormulit;
                        }

//                        cout<<"mkl "<<temfactortermsto<<endl;
//                        cout<<"mkl2 "<<quoexprfactormulit<<endl;
//                        cout<<"factortermsetmkl "<<factortermset<<endl;
                        if(factortermset.find(temfactortermsto)!=factortermset.end()){
                            factortermclt.insert(quoexprfactormulit);
//                            cout<<"factortermcltmkl2 "<<factortermclt<<endl;
                            temallterms=_ex0;
                            break;
                        }
                    }


                    if(!temallterms.is_equal(_ex0)){
                        ///The factors which are present in both quoexprfactor and factclt is selected.
                        /// The constant factors is also collected.
                        ///The factors without constant factors is assigned to temfactorterm.
                        if(is_a<add>(quoexprfactor)){
                            if (find(factclt.begin(),factclt.end(),quoexprfactor)!=factclt.end())
                                temfactorterm=quoexprfactor;
                            else break;
                        }

                        else{
                            iswhileloopbreak=true;
                            //temfactorterm without constant factor
                            for(const_iterator itr=quoexprfactor.begin();itr!=quoexprfactor.end();++itr){
                                if(rem(temallterms,expand(*itr),_var).is_equal(remexpr)){
//                                    cout<<"uiop "<<*itr<<endl;
                                    if ((*itr).has(_var)) {
                                        if (is_a<power>(*itr) && is_a<add>((*itr).op(0))) {
                                            if (find(factclt.begin(),factclt.end(),(*itr).op(0))!=factclt.end()) {
                                                temfactorterm=temfactorterm*(*itr);
                                                iswhileloopbreak=false;
                                            }
                                        }
                                        else if (find(factclt.begin(),factclt.end(),*itr)!=factclt.end()){
                                            temfactorterm=temfactorterm*(*itr);
                                            iswhileloopbreak=false;
//                                            cout<<"uiop1 "<<temfactorterm<<endl;
                                        }
                                    }
                                }
                            }
                        }
                        if(iswhileloopbreak) break;


                        /// Quotient of temallterms-remexpr (divided by temfactorterm) is again divided
                        /// by temfactorterm, and then the reamainder is factored.
                        /// If the factored term is constant, is assigned to constantfactor, otherwise
                        /// is multiplied with temfactorterm.
                        /*cout<<"qwer "<<temfactorterm<<endl;
                        cout<<"qwer1 "<<temallterms-remexpr<<endl*/;
                        //cout<<quo(temallterms-remexpr,temfactorterm,_var)<<endl;
                        //ex quoexpr2=temallterms-remexpr;
                        remfactor2=_ex0;
                        if(!factortermset.empty()){
                            ex quoexpr2=temallterms-remexpr;
                            while(remfactor2.is_equal(_ex0)){
                                quoexpr2=quo(quoexpr2,lowestfactorterm,_var);
                                remfactor2=rem(quoexpr2,lowestfactorterm,_var);
                            }
                            remfactor2=factor(remfactor2);
                        }
                        else {
                            ex quoexpr2=temallterms-remexpr;
                            remfactor2=factor(rem(quo(quoexpr2,temfactorterm,_var),temfactorterm,_var));
                        }

//                        cout<<"uiop3 "<<remfactor2<<" "<<temfactorterm<<endl;
                        remfactor2=(remfactor2*externSymbols.symb_);//Because symb_ will factor numbers, Ex: (5*x+10)*symb_=5*(x+2)*symb_
                        constantfactor=_ex1;
                        //if (is_a<mul>(remfactor2)) {
                            for(const_iterator itr=(remfactor2).begin();itr!=(remfactor2).end();++itr){
                                if((*itr).has(_var))
                                    temfactorterm=temfactorterm*(*itr);
                                else if(!(*itr).is_equal(_ex0) && !(*itr).has(externSymbols.symb_))// The constant factors is assigned to constantfactor.
                                    constantfactor=constantfactor*(*itr);
                            }
                        //}
//                        else{
//                            if(remfactor2.has(_var))
//                                temfactorterm=temfactorterm*remfactor2;
//                            else if(!remfactor2.is_equal(_ex0))// The constant factors is assigned to constantfactor.
//                                constantfactor=constantfactor*remfactor2;
//                        }
//                        cout<<"temfactorterm "<<temfactorterm<<endl;
                        if ((temfactorterm*constantfactor).is_equal(factortermprev)) {//present factor term cannot be equal to the previous factor term
                            soluCltPoly={};
                            return {};
                        }

                        ///GCD of the powers of each factor terms is calculated
                        ///  and their powers are multiplied with 1/GCD
                        if(is_a<mul>(temfactorterm) && temfactorterm.has(_var)){
                            powTermClt.remove_all();
                            for(const_iterator itr=temfactorterm.begin();itr!=temfactorterm.end();++itr){
                                if (is_a<power>(*itr) && (*itr).has(_var)) {
                                    powTermClt.append((*itr).op(1));
                                }
                                else if((*itr).has(_var)) powTermClt.append(1);
                            }
                            ex GCD =Gcd(powTermClt);
                            if(!GCD.is_equal(_ex1)){
                                temfactortermsto=_ex1;
                                for(const_iterator itr=temfactorterm.begin();itr!=temfactorterm.end();++itr){//simplify (z^a)^1/GCD=x^(a/GCD)
                                    if (is_a<power>(*itr) && (*itr).has(_var)) {
                                        temfactortermsto=temfactortermsto*pow((*itr).op(0), (*itr).op(1)*1/GCD);
                                    }
                                    else{
                                        temfactortermsto=temfactortermsto*(*itr);
                                    }
                                }
                            }
                            else {
                                temfactortermsto=temfactorterm;
                            }
                        }
                        else {
                            if (is_a<power>(temfactorterm)) {
                                temfactortermsto=temfactorterm.op(0);
                            }
                            else temfactortermsto=temfactorterm;
                        }

                        ///If factortermset has more than one term solution is failure.
                        factortermset.insert(temfactortermsto);
                        if(factortermset.size()>1)
                            break;

                        factortermclt.insert(temfactorterm*constantfactor);
                        factortermprev=temfactorterm*constantfactor;
                        if(factortermclt.size()==1){
                            factortermclt.insert(remexpr);
                            lowestfactorterm=temfactorterm;
                        }

                        temallterms=(temallterms-expand(temfactorterm*constantfactor+remexpr));
//                        cout<<"temallterms "<<temallterms<<endl;
                        degnow=degree(temallterms,_var);
                        if(degnow!=deg){//checking whether degree is equal to previous.
                            break;//break while loop
                        }
                        deg=degnow;
                        temfactorterm=*it;
                    }
                }

                if(temallterms.is_equal(_ex0) && !factortermclt.empty()){
                    ex factorterm = *factortermset.begin();
                    ex factorsum = std::accumulate(factortermclt.begin(),factortermclt.end(),ex(0));
//                    cout<<"factorsum "<<factorsum<<endl;
                    const string str="Zz_"+std::to_string(symNum);
                    ex Zz_=generator.symGenerator(str);
                    generator.symRegister(Zz_);
                    symNum=symNum+1;
//                    lst powTermClt;//collector of degree of each term in factorterm
//                    for(const_iterator itr=factorterm.begin();itr!=factorterm.end();++itr){
//                        if (is_a<power>(*itr) && (*itr).has(_var)) {
//                            powTermClt.append((*itr).op(1));
//                        }
//                        else powTermClt.append(1);
//                    }
//                    ex GCD =Gcd(powTermClt);
//                    cout<<"GCD "<<GCD<<endl;
//                    cout<<"GCD "<<powTermClt<<endl;
//                    cout<<"factorterm1 "<<factorterm<<endl;

//                    if(!is_a<add>(factorterm)){
//                        ex temfactorterm=(factorterm);
//                        factorterm=_ex1;
//                        for(const_iterator itr=temfactorterm.begin();itr!=temfactorterm.end();++itr){//simplify (z^a)^1/GCD=x^(a/GCD)
//                            if (is_a<power>(*itr) && (*itr).has(_var)) {
//                                factorterm=factorterm*pow((*itr).op(0), (*itr).op(1)*1/GCD);
//                            }
//                            else{
//                                factorterm=factorterm*(*itr);
//                            }
//                        }
//                    }
                    //cout<<"factorterm2 "<<factorterm<<endl;
                    factorsum=factorsum.subs(factorterm==Zz_,subs_options::algebraic);
                    if(!factorsum.has(_var)){ //return polySolve(_equ,_var,2);//second try to solve the equations like: x^4+x^2+c=0
                        //cout<<"factorsum "<<factorsum<<endl;
                        solucheck=polySolve(factorsum,Zz_,2);

                        //cout<<"factorterm-Zz_ "<<factorterm-Zz_<<endl;
                        if(nops(soluCltPoly)!=0){
                            solucheck=polySolve(factorterm-Zz_,_var,1);
                            if (soluCltPoly.has(Zz_)){
                                soluCltPoly={};
                                //return {};
                            }
                        }
                        else{
                            soluCltPoly={};
                            //return {};
                        }



                    }
                }
                //if(!factorterm.has(_var) || !temallterms.is_equal(_ex0)) return polySolve(_equ,_var,2);//second try to solve the equations like: x^4+x^2+c=0
                factortermclt.clear();
            }
        }
        else {//catching the equations like: x^4+x^2+c=0
            ex GCD=_ex1;
            lst powTermClt;//collector of degree of each factor term
            //cout<<"alleq "<<allterms<<endl;
            for (const_iterator itr=allterms.begin(); itr!=allterms.end(); ++itr){
                powTermClt.append(degree(*itr,_var));
            }
//            cout<<"powTermClt "<<powTermClt<<endl;
            GCD=Gcd(powTermClt);

            if(GCD.is_equal(_ex1)){
                soluCltPoly={};
                return {};
            }
            if (powTermClt.nops()>2 && allterms.degree(_var)/GCD>2) {
                soluCltPoly={};
                return {};
            }

            const string str="Zz_"+std::to_string(symNum);
            ex Zz_=generator.symGenerator(str);
            generator.symRegister(Zz_);
            symNum=symNum+1;
            allterms=allterms.subs(pow(_var,GCD)==Zz_,subs_options::algebraic);
            //cout<<"alleq "<<allterms<<endl;
            //solving quadratic,cubic,xnc//
            polySolve(allterms,Zz_,3);
            //Solving equations x^GCD=A//
            lst temsoluCltPoly,temsoluCltPoly1;
            //cout<<"soluCltPoly "<<soluCltPoly<<endl;
            if(nops(soluCltPoly)!=0 && GCD!=_ex1){
                for(lst::const_iterator itr=soluCltPoly.begin();itr != soluCltPoly.end();itr++){
                    temsoluCltPoly1=xnc(_var,GCD,(*itr).rhs());
                    //cout<<"temsoluCltPoly1 "<<temsoluCltPoly1<<endl;
                    for(lst::const_iterator itr=temsoluCltPoly1.begin();itr!=temsoluCltPoly1.end();itr++){
                        temsoluCltPoly.append(*itr);
                    }
                }
                soluCltPoly=temsoluCltPoly;
            }

            if (soluCltPoly.has(Zz_)){
                soluCltPoly={};
                return {};
            }

        }

        if(nops(soluCltPoly)==0)
            return polySolve(_equ,_var,2);


    return soluCltPoly;
}


/** getting solutions of a polynomial equation **/
int solvec::one_eq_solutions(const ex& _equ, const ex& _var)
{
    one_eq_solu.remove_all();

    if(!_equ.has(_var))
        return 0;

    lst temSolu;

    if((is_a<power>(_equ)&&is_a<add>(_equ.op(0)))
       ||(is_a<add>(_equ)))
    {
        soluCltPoly.remove_all();
        temSolu = polySolve(_equ,_var);

        if(nops(temSolu != 0))
        {
            for(auto it = temSolu.begin(); it != temSolu.end(); it++)
            {
                if(!one_eq_solu.has(*it))
                    one_eq_solu.append(*it);
            }
        }
    }
    else
    {
        try
        {

            if((_equ).subs(_var == _ex0)==_ex0)
                one_eq_solu.append(_var == _ex0);
        }
        catch(ginacsym::pole_error){return 0;}
        catch(ginacsym::indeterminate_error){return 0;}
    }
    if(nops(one_eq_solu) == _ex0)
            return 0;
    return 1;
}

/** solution variables are sorted with ascending order of degree of variables in poly equation (eqDivider[j]) **/
lst solvec::varOrderByDeg(const lst& low_var, map<unsigned, ex>& eqDivider, unsigned& eqDividerSz)
{
    lst low_var_sep, low_var_sep_wtotpoly;
    if(eqDividerSz > eqDivider.size())
       return low_var_sep;


    std::vector<std::pair<ex, int>> eq_degnum_pairs;

    do
    {
          for( auto j =  low_var.begin(); j !=  low_var.end(); j++)
          {
             if((eqDivider[eqDividerSz]).has(*j) && is_polynomial(eqDivider[eqDividerSz],*j))
             {
                eq_degnum_pairs.push_back(make_pair(*j, degree(eqDivider[eqDividerSz],*j)));
             }
             else if((eqDivider[eqDividerSz]).has(*j))
                low_var_sep_wtotpoly.append(*j);  // non-polynomial variables are collected
          }
          if(!eq_degnum_pairs.empty())
          {
              sort(eq_degnum_pairs.begin(), eq_degnum_pairs.end(), [=](std::pair<ex, int>& a, std::pair<ex, int>& b){
                  return a.second < b.second;}); // sorting of polynomial variables

              for(auto itr = eq_degnum_pairs.begin(); itr != eq_degnum_pairs.end(); itr++)
              {
                  low_var_sep.append(itr->first);
              }

          }
          if(nops(low_var_sep_wtotpoly) != 0)
          {
              for(auto itr = low_var_sep_wtotpoly.begin(); itr != low_var_sep_wtotpoly.end(); itr++)
              {
                  low_var_sep.append(*itr);
              }
          }
          if(nops(low_var_sep) != 0)
             return low_var_sep;

              eqDividerSz++; // shifting to next equation

    }while(eqDividerSz < eqDivider.size());

   return low_var_sep;
}

// checking present of variables (_var) in _expr
bool solvec::isVarPrsnt(const ex &_expr, const exset &_var)
{

    bool funcPrsnt = false;
    for( auto itr =  _var.begin(); itr !=  _var.end();)
    {

        if(_expr.has(*itr))
        {
            funcPrsnt = true;
            itr = _var.end();
        }
        else
        {
            itr++;
        }
    }

    return funcPrsnt;

}

ex solvec::sysequ_red(const exset& sysequ_, const exset& var_)
{
    /// collecting solutions ///
    if(sysequ_.empty())
    {
        solu.insert(soluClt);
    }
    else
    {
        try
        {
            /// Eliminating variables ///
            // selecting equations with the lowest number of solution variables
           lst low_var, var_in_eq;
           ex low_var_eq, ret, denoma;
           exset sysequ = sysequ_;
           ex subs_simp;
           bool isSolu;

           var_in_eq.remove_all();

           std::vector<size_t> addNumFrEchtrmIneq;
           std::vector<std::pair<ex, unsigned>> maxAddnum;
           std::map<ex,unsigned,ex_is_less> totalAddnum;

           for (auto itr = sysequ.begin(); itr != sysequ.end(); ++itr)
           {
               addNumFrEchtrmIneq.clear();
               bool isVarprsntInEq = false;
               for( auto j =  var_.begin(); j !=  var_.end(); j++) // checking present of minimum one solution-var
               {                                                   // in each equations.
                   if((*itr).has(*j))
                       isVarprsntInEq = true;
               }
               if(!isVarprsntInEq) // if minimum one solution-var not present
                   return _ex_1;   // solutions do not exist.

               if(is_a<add>(*itr))
               {
                   if(isVarPrsnt(*itr, var_))
                   {
                       totalAddInEqV.addNum = 0;
                       totalAddInEqV.expr_visitor(*itr);
                       addNumFrEchtrmIneq.push_back(totalAddInEqV.addNum);
                   }
                   else
                   {
                       addNumFrEchtrmIneq.push_back(0);
                   }
               }

               else if(is_a<power>(*itr) && is_a<add>((*itr).op(0)))
               {
                   if(isVarPrsnt((*itr).op(0), var_))
                   {
                       totalAddInEqV.addNum = 0;
                       totalAddInEqV.expr_visitor((*itr).op(0));
                       addNumFrEchtrmIneq.push_back(totalAddInEqV.addNum);
                   }
               }

               else if(is_a<mul>(*itr))
               {
                   for (size_t i = 0; i<nops(*itr);i++)
                   {
                       if(is_a<add>((*itr).op(i)))
                       {
                           if(isVarPrsnt((*itr).op(i), var_))
                           {
                               totalAddInEqV.addNum = 0;
                               totalAddInEqV.expr_visitor((*itr).op(i));
                               addNumFrEchtrmIneq.push_back(totalAddInEqV.addNum);
                           }
                       }
                       else if(is_a<power>((*itr).op(i)) && is_a<add>((*itr).op(i).op(0)))
                       {
                           if(isVarPrsnt((*itr).op(0), var_))
                           {
                               totalAddInEqV.addNum = 0;
                               totalAddInEqV.expr_visitor((*itr).op(i).op(0));
                               addNumFrEchtrmIneq.push_back(totalAddInEqV.addNum);
                           }
                       }
                       else
                       {
                           if(isVarPrsnt((*itr).op(i), var_))
                           {
                               addNumFrEchtrmIneq.push_back(0);
                           }
                       }

                   }
               }

               else
               {
                   if(isVarPrsnt((*itr), var_))
                   {
                       addNumFrEchtrmIneq.push_back(0);
                   }
               }

               maxAddnum.push_back(make_pair(*itr, *max_element(addNumFrEchtrmIneq.begin(),addNumFrEchtrmIneq.end())));
               totalAddnum[*itr] = accumulate(addNumFrEchtrmIneq.begin(), addNumFrEchtrmIneq.end(), 0);
           }

           sort(maxAddnum.begin(), maxAddnum.end(), [=](std::pair<ex, unsigned>& a, std::pair<ex, unsigned>& b){
               return a.second < b.second;}); // sorting in ascending order by maximum number of add in each equation

           unsigned minadd = maxAddnum.begin()->second;

           std::vector<std::pair<ex, unsigned>> temMinAddnum;

           for(auto itr = maxAddnum.begin(); itr != maxAddnum.end(); itr++)
           {
               if((itr->second)==minadd)
                   temMinAddnum.push_back(make_pair(itr->first,totalAddnum[itr->first]));
           }
           if(temMinAddnum.size()>1)
           {
               sort(temMinAddnum.begin(),temMinAddnum.end(),[=](std::pair<ex, unsigned>& a, std::pair<ex, unsigned>& b){
                   return a.second < b.second;}); // sorting in ascending order by total number of add in each equation

               minadd = temMinAddnum.begin()->second;

               std::vector<std::pair<ex, unsigned>> temMinVarnum;

               for(auto itr = temMinAddnum.begin(); itr != temMinAddnum.end(); itr++)
               {
                   if((itr->second)==minadd)
                       temMinVarnum.push_back(make_pair(itr->first,totalAddnum[itr->first]));
               }
               if(temMinVarnum.size()>1)
               {
                   std::vector<std::pair<ex, unsigned>> eq_varnum_pairs;
                   std::map<ex, lst, ex_is_less> eq_var_pairs;

                   for (auto itr = temMinVarnum.begin(); itr != temMinVarnum.end(); ++itr)
                   {
                       for( auto j =  var_.begin(); j !=  var_.end(); j++)
                       {
                           if((itr->first).has(*j))
                               var_in_eq.append(*j);
                       }

                       eq_varnum_pairs.push_back(make_pair(itr->first, nops(var_in_eq)));
                       var_in_eq.remove_all();
                   }
                   sort(eq_varnum_pairs.begin(), eq_varnum_pairs.end(), [=](std::pair<ex, unsigned>& a, std::pair<ex, unsigned>& b){
                       return a.second < b.second;}); // sorting in ascending order by number of var
                   temMinAddnum = eq_varnum_pairs;
               }


           }

           low_var_eq = temMinAddnum.begin()->first;

           if(!nops(var_in_eq))
           {
               for( auto j =  var_.begin(); j !=  var_.end(); j++)
               {
                   if((low_var_eq).has(*j))
                       var_in_eq.append(*j);
               }
           }


           low_var = var_in_eq;


           if(nops(low_var) == 0 || low_var_eq == _ex0)
                return _ex_1;

           exset SysEquClt2;

           unsigned var_soluClt;

           const ex low_var_eq2 = Simplify(collect_common_factors(Factor(low_var_eq)));
           map<unsigned, ex> eqDivider;
           unsigned eqDividerSz = 0;

           if(is_a<mul>(low_var_eq2)) // each factor of Low variable equation is separated by
           {                          // storing into eqDivider. eqDividerSz traces each separated equations.
                ex tem1 =_ex1;
                for(unsigned j = 0; j < nops(low_var_eq2); j++)
                {
                    if(isVarPrsnt((low_var_eq2.op(j)), var_))
                    {
                        if((is_a<power>(low_var_eq2.op(j))&&is_a<add>(low_var_eq2.op(j).op(0)))
                            ||(is_a<add>(low_var_eq2.op(j))))
                        {eqDivider[eqDividerSz] = low_var_eq2.op(j); eqDividerSz++;}
                        else //if(!is_a<numeric>(low_var_eq2.op(j)))
                            tem1 = tem1*low_var_eq2.op(j);
                    }

                }
                if(tem1!=_ex1)
                    {eqDivider[eqDividerSz] = tem1;}
           }
           else if(isVarPrsnt((low_var_eq2), var_))
              eqDivider[0] = low_var_eq2;

           lst low_var_sep;


           eqDividerSz = 0;
           low_var_sep = varOrderByDeg(low_var, eqDivider, eqDividerSz); // solution variables of separated equations are sorted
           lst::const_iterator solu_var = low_var_sep.begin();


           do
           {
                int solu_ext = 0;
                lst tem_one_solu;
                solu_ext = this->one_eq_solutions(Simplify(numer(eqDivider[eqDividerSz])), (*solu_var)); // attempt 1 for getting solutions
                if(nops(one_eq_solu))
                {
                    lst one_eq_solu_test = {};
                    for(auto itr1 = one_eq_solu.begin(); itr1 != one_eq_solu.end(); itr1++)
                    {
                        //if(fullSimplify((numer(eqDivider[eqDividerSz])).subs(*itr1))==_ex0)//solution check
                            one_eq_solu_test.append(*itr1);
                    }

                    one_eq_solu = one_eq_solu_test;
                    if(nops(one_eq_solu))
                        solu_ext =1;
                    else
                    {
                        solu_ext = 0;
                    }
                }
                if(solu_ext) // avoiding pole error
                {
                    lst one_solu_fltr={};
                    for(auto itr1 = one_eq_solu.begin(); itr1 != one_eq_solu.end(); itr1++)
                    {
                        isSolu = true;

                        for(auto j = sysequ.begin(); j != sysequ.end();)
                        {
                            denoma = denom(*j);
                            if(denoma != _ex1 && denoma.has((*solu_var)))
                            {
                                try
                                {
                                    subs_simp = (simplify((denoma).subs(*itr1)));
//                                    cout<<"subs_simp "<<subs_simp<<endl;
                                    if((is_a<numeric>(subs_simp)  || (is_a<numeric>(subs_simp) && subs_simp.info(info_flags::positive)
                                                                      && subs_simp < Gtolerance) ||
                                        (is_a<numeric>(subs_simp) && subs_simp.info(info_flags::negative) && -subs_simp < Gtolerance) ||
                                         (subs_simp.has(Infinity) || subs_simp.has(-Infinity))))
                                    {
                                        isSolu = false;
                                        j = sysequ.end();
                                    }
                                    else
                                        j++;

                                }
                                catch(ginacsym::pole_error){isSolu = false; j = sysequ.end();}
                                catch(ginacsym::indeterminate_error){isSolu = false; j = sysequ.end();}
                            }
                            else
                                j++;

                        }

                        if(isSolu)
                        {
                            one_solu_fltr.append(*itr1);
                        }
                    }

                    if(nops(one_solu_fltr)==0)
                    {
                        one_eq_solu.remove_all();
                        solu_ext = 0;
                    }
                    else
                        one_eq_solu = one_solu_fltr;

                }

               if(nops(one_eq_solu) != 0)
               {
//                    cout<<"one_eq "<<one_eq_solu<<endl;

                  if(sysequ.find(low_var_eq)!=sysequ.end())
                    sysequ.erase(low_var_eq);
                   if(nops(one_eq_solu) != 0)
                     tem_one_solu = one_eq_solu;

                   one_eq_solu.remove_all();

                   var_soluClt = nops(soluClt);

                   for(lst::const_iterator k = tem_one_solu.begin(); k != tem_one_solu.end(); k++) // searching final solutions taking each solution of low variable equation
                   {

                       soluClt.append((*k).lhs() == Simplify(Factor(numer((*k).rhs())))/Simplify(Factor(denom((*k).rhs()))));

                       for(auto j = sysequ.begin(); j != sysequ.end(); j++)
                       {
                            try
                            {
                                subs_simp = numer(simplify(numer((*j)).subs(simplify(*k))));
//                                cout<<subs_simp <<endl;

                                if(subs_simp.has(Infinity) || subs_simp.has(-Infinity)) return _ex_1;// ginacsym Bugs: wrong numer
                            }                                                                        // numer(1/2*b/((1 + 3*sqrt(a)*(-2 + 9*a)^(-1/2))*(-1 + 3*sqrt(a)*(-2 + 9*a)^(-1/2))));
                            catch(ginacsym::pole_error){return _ex_1;}                                  //  -> -(-2+9*a)*b
                            catch(cln::runtime_exception){return _ex_1;}                             // To avoid Bugs: get numer after simplify

                            catch(ginacsym::indeterminate_error){return _ex_1;}

                            if( !is_a<numeric>(subs_simp) ||
                               (is_a<numeric>(subs_simp) && subs_simp.info(info_flags::positive) && subs_simp > Gtolerance) ||
                                (is_a<numeric>(subs_simp) && subs_simp.info(info_flags::negative) && -subs_simp > Gtolerance)){
                                SysEquClt2.insert(subs_simp);
                            }

                       }

                       SysEquCltEnv = SysEquClt2;

//                       for(auto it:SysEquClt2) cout<<"it "<<it<<endl;

                       const ex ret = this->sysequ_red(SysEquClt2,  var_);

                       if(nops(soluClt) - (var_soluClt) == 1)
                       {
                            soluClt.remove_last();
                       }

                        SysEquClt2.clear();
                   }
                }

                solu_var++;

                if(eqDivider.size() > (eqDividerSz + 1) && solu_var == low_var_sep.end()) // the solution process is restarted
                {                                                                         // for next equation in eqDivider.
                    eqDividerSz++;

                    low_var_sep = varOrderByDeg(low_var, eqDivider, eqDividerSz);
                    if(nops(low_var_sep != 0))
                        solu_var = low_var_sep.begin();
                    else
                        solu_var = low_var_sep.end();

                }
                else if(eqDivider.size() > (eqDividerSz + 1) && SysEquCltEnv.empty())  // the solution process for current equation is stopped and
                {                                                                      // we do not get the solutions for other variables.
                    eqDividerSz++;                                                    // the solution process is restarted
                    low_var_sep = varOrderByDeg(low_var, eqDivider, eqDividerSz);      // for next equation in eqDivider.
                    if(nops(low_var_sep != 0))
                        solu_var = low_var_sep.begin();
                    else
                        solu_var = low_var_sep.end();
                }
                else if(SysEquCltEnv.empty() && ((is_a<power>(eqDivider[eqDividerSz])&&is_a<add>(eqDivider[eqDividerSz].op(0)))
                                                ||(is_a<add>(eqDivider[eqDividerSz])))) // reaches at maximum equation and the solution
                    {solu_var = low_var_sep.end();}                                 // process for current equation is stopped.

            }while(solu_var != low_var_sep.end());
        }

        catch(ginacsym::pole_error){return _ex_1;}
        catch(ginacsym::indeterminate_error){return _ex_1;}
        catch (cln::runtime_exception){return _ex_1; }

        catch(std::invalid_argument){return _ex_1; }
        catch(std::out_of_range){return _ex_1;}



    }

    return _ex1;
}

/** All solutions take the shorten forms by repeated substitutions.  **/
exsetlst solvec::solu_subs(exsetlst solu_)
{
    exsetlst solu_wt_subs;
    lst tem;
    ex xprev, xnow;
    bool den_zero;

   /// solutions are substituted by other solutions
    for(exsetlst::const_iterator it = solu_.begin(); it != solu_.end(); it++)
    {
//        cout<<"lopjg "<<*it<<endl;
        unsigned i = 0;
        den_zero = false;
        exset lst_exset;
        lst exset_lst;
        do
        {
            xnow = ((*it).op(i)).rhs();
            den_zero = false;
            do
            {
                xprev = (xnow);
                try
                {
                    xnow = Simplify((xprev)).subs((*it), subs_options::algebraic);//here simplify to Simplify increases computation speed
                    if (xnow.has(Infinity) || xnow.has(-Infinity)) {
                        den_zero=true;
                    }
                }
                catch(ginacsym::pole_error){den_zero = true;}
                catch(ginacsym::indeterminate_error){den_zero = true;}

            } while(xprev != xnow && den_zero == false);
            if(den_zero == false)
                tem.append(((*it).op(i)).lhs() == xnow);
         i = i + 1;
        }while(den_zero == false && i < nops(*it));

        if(den_zero == false)
        {
            lst_exset.insert(tem.begin(), tem.end());
            for(exset::const_iterator it = lst_exset.begin(); it != lst_exset.end(); it++)
            {
                exset_lst.append(*it);
            }
            solu_wt_subs.insert(exset_lst);
            exset_lst.remove_all();
            lst_exset.clear();
        }
        tem.remove_all();
    }


    /// the presence of sub-solutions in each solutions are checked. If sub-solution present, the solutions
    /// are removed.
    vector<std::pair<lst, unsigned>> eq_nops_pairs;
    for(exsetlst::const_iterator it = solu_wt_subs.begin(); it != solu_wt_subs.end(); it++)
    {
       eq_nops_pairs.push_back(make_pair(*it, nops(*it)));
    }
    sort(eq_nops_pairs.begin(), eq_nops_pairs.end(), [=](std::pair<lst, unsigned>& a, std::pair<lst, unsigned>& b){
    return a.second < b.second;});

    for(vector<std::pair<lst, unsigned>>::const_iterator it1 = eq_nops_pairs.begin(); it1 != (eq_nops_pairs.end()); it1++)
    {
        vector<std::pair<lst, unsigned>>::const_iterator it3 = it1 + 1;
        for(auto it4 = (it3); it4 != (eq_nops_pairs).end(); it4++)
        {
            unsigned lst_num = 0;
            for(lst::const_iterator it2 = (it1->first).begin(); it2 != (it1->first).end(); it2++)
            {
                for(lst::const_iterator it5 = ((it4)->first).begin(); it5 != (it4->first).end(); it5++)
                {
                    if((*it2) == (*it5))
                        lst_num = lst_num + 1;
                }
            }

            if(lst_num == nops(it1->first))
            {
                solu_wt_subs.erase((it4->first));
            }

        }

    }

    return solu_wt_subs;
}
/////////////////////////////////////////////////////////////

exsetlst solvec::operator()(const lst & equ_, const lst& var_)
{
    ex numera, denoma, subs_imp;
    exset _var, sysequ;
    exset equ_set;
    exsetlst temsolu_setlst,solu_setlst;
    map<unsigned, exset> eqDivider, temeqDivider;

    try
    {

        for (lst::const_iterator i = var_.begin(); i != var_.end(); ++i)
        {
           _var.insert(*i);
        }

        for (lst::const_iterator i = equ_.begin(); i != equ_.end(); ++i)
        {
            if(!is_a<relational>(*i))
                numera = simplify(numer(*i));
            else
                numera = simplify(numer(*i).lhs()-numer(*i).rhs());

            for( auto itr = _var.begin(); itr != _var.end(); itr++ )
            {
                funcpresent funcpresent(*itr);
                funcpresent.expr_visitor(numera);
                if(funcpresent.funcpresence || funcpresent.varInPow) // presence of any functions with solution variables,
                    return solu_setlst;                              // presence of solution variables in power are not supported.
            }

           if(numera != _ex0)
           {
                equ_set.insert(numera);
           }

        }

//        for(auto it: equ_set) cout<<"kldaa "<<it<<endl;
        //Handling single equation
        if (equ_set.size()==1 and _var.size()==1) {
            ex single_equ=factor(expand(*equ_set.begin()));
            lst temsolu_lst;
            if (is_a<mul>(single_equ)) {
                for (int i = 0; i < single_equ.nops(); ++i) {
                    if (single_equ.op(i).has(*_var.begin())) {
                        if (single_equ.op(i).degree(*var_.begin())<=2) {
                            temsolu_lst=this->quadratic(single_equ.op(i),*_var.begin());
                            if(temsolu_lst.nops()!=0){
                                for (int j = 0; j < temsolu_lst.nops(); ++j) {
                                    temsolu_setlst.insert(lst{temsolu_lst.op(j)});
                                }
                            }
                        }
                        else{
                            if (single_equ.op(i).degree(*var_.begin())==3) {
                                temsolu_lst=this->cubics(single_equ.op(i),*_var.begin());
                                if(temsolu_lst.nops()!=0){
                                    for (int j = 0; j < temsolu_lst.nops(); ++j) {
                                        temsolu_setlst.insert(lst{temsolu_lst.op(j)});
                                    }
                                }
                            }
                            else {
//                                temsolu_lst=this->Nquartic(single_equ.op(i),*_var.begin());
//                                if(temsolu_lst.nops()!=0){
//                                    for (int j = 0; j < temsolu_lst.nops(); ++j) {
//                                        temsolu_setlst.insert(lst{temsolu_lst.op(j)});
//                                    }
//                                }
//                                else{
                                    temsolu_lst=this->polySolve(single_equ.op(i),*_var.begin());
                                    if(temsolu_lst.nops()!=0){
                                        for (int j = 0; j < temsolu_lst.nops(); ++j) {
                                            temsolu_setlst.insert(lst{temsolu_lst.op(j)});
                                        }
                                    }
//                                }
                            }
                        }
                    }
                }
            }
            else{
                if (single_equ.degree(*var_.begin())<=2) {
                    temsolu_lst=this->quadratic(single_equ,*_var.begin());
                    if(temsolu_lst.nops()!=0){
                        for (int j = 0; j < temsolu_lst.nops(); ++j) {
                            temsolu_setlst.insert(lst{temsolu_lst.op(j)});
                        }
                    }
                }
                else{
                    if (single_equ.degree(*var_.begin())==3) {
                        temsolu_lst=this->cubics(single_equ,*_var.begin());
                        if(temsolu_lst.nops()!=0){
                            for (int j = 0; j < temsolu_lst.nops(); ++j) {
                                temsolu_setlst.insert(lst{temsolu_lst.op(j)});
                            }
                        }
                    }
                    else {
//                        temsolu_lst=this->Nquartic(single_equ,*_var.begin());
//                        if(temsolu_lst.nops()!=0){
//                            for (int j = 0; j < temsolu_lst.nops(); ++j) {
//                                temsolu_setlst.insert(lst{temsolu_lst.op(j)});
//                            }
//                        }
//                        else{
                            temsolu_lst=this->polySolve(single_equ,*_var.begin());
                            if(temsolu_lst.nops()!=0){
                                for (int j = 0; j < temsolu_lst.nops(); ++j) {
                                    temsolu_setlst.insert(lst{temsolu_lst.op(j)});
                                }
                            }
//                        }
                    }
                }
            }
            return temsolu_setlst;
        }


        if(!equ_set.empty())
            this->sysequ_red(equ_set, _var);
        if(!solu.empty())
            temsolu_setlst = this->solu_subs(solu);

//        bool notSolu;
        if(!temsolu_setlst.empty()){
        for(auto itr = temsolu_setlst.begin();itr!=temsolu_setlst.end();itr++){
    //            notSolu = false;
    //            for (auto itr1 = equ_set.begin();itr1 != equ_set.end();)//solution check
    //            {
    //                if(fullSimplify((*itr1).subs(*itr))!=_ex0)
    //                {
    //                    notSolu =true;
    //                    itr1 = equ_set.end();
    //                }
    //                else
    //                {
    //                    itr1++;
    //                }
    //            }

    //            if(!notSolu)
                    solu_setlst.insert(*itr);
            }
        }
        else{

            return solu_setlst;
        }
    }

    catch(ginacsym::pole_error){return solu_setlst;}
    catch (cln::runtime_exception){return solu_setlst;}
    catch(ginacsym::indeterminate_error){return solu_setlst;}

    catch(std::invalid_argument){return solu_setlst;}
    catch(std::out_of_range){return solu_setlst;}
    //catch(std::runtime_error){return solu_setlst;}
    //catch(std::range_error){return solu_setlst;}
    //catch(std::logic_error){return solu_setlst;}
    //catch(std::domain_error){return solu_setlst;}
    return temsolu_setlst;
}
}
/////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////







