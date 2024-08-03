
/** @file simplify.cpp
 *
 *  Implementation of simplify function.
    It simplify algebraic expressions.**/

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

#include<cln/exception.h>
#include "ginacwrapper.h"
#include "inert.h"
#include "infinity.h"
#include "normal.h"
#include "utility.h"
#include "inifcns.h"
#include "simplify.h"
#include "mul.h"
#include "power.h"
#include "add.h"

//#include "solve.h"
//#include "F_expns_methd.h"
//#include "fim.h"


namespace ginacsym{

    size_t expandLevel = 20,addNumFrFactr = 10;
    numeric largstNumsimp="10000000000000000000000000000000"; /* expandLevel: To expand an expression upto a specified  degree (used in solvec::polySoluWtAutoDegSelct)
                                              // addNumFrFactr: To get factor upto specific number of "add" present (used in Factor in utility.cpp)
                                              // largstNumsimp: To get prime factors upto a specific number.(used in numSimplify::expr_visitor )
                                               */

    // A function to get all prime factors of a given number n
    std::map<numeric,numeric> primeFactors(numeric n)
    {
        std::map<numeric,numeric> primeNum;

        while (irem(n,_numeric2) == 0)
        {
            primeNum[2]=primeNum[2]+_numeric1;
            n = n/_numeric2;
        }

        // n must be odd at this point. So we can skip
        // one element (Note i = i +2)
        for (numeric i = _numeric3; i <= ginacsym::sqrt(n); i = i+_numeric2)
        {
            // While i divides n, print i and divide n
            while (irem(n,i) == 0)
            {
                primeNum[i]=primeNum[i]+_numeric1;
                n = n/i;
            }
        }

        // This condition is to handle the case when n
        // is a prime number greater than 2
        if (n > _numeric2)
        {
            primeNum[n]=primeNum[n]+_numeric1;
        }

        return primeNum;
    }
    // Adding even, odd nature of trigonmetric,hyperbolic functions and (-5)^(7/2) = -125sqrt(5)*I
    ex TrigArgSign_Complx::expr_visitor(const ex & e)
    {
        if (is_a<power>(e) && e.op(0).info(info_flags::negative)&& (2*e.op(1)).info(info_flags::odd)){
            return I*sqrt(-e.op(0))*pow(-e.op(0),e.op(1) - _ex1_2);
        }
        else if (is_ex_the_function(e, sin) || is_ex_the_function(e, tan) ||
                 is_ex_the_function(e, csc) || is_ex_the_function(e, cot)||
                 is_ex_the_function(e, sinh) || is_ex_the_function(e, tanh) ||
                 is_ex_the_function(e, csch) || is_ex_the_function(e, coth))
        {
            var_ = collect_common_factors(e.op(0)*externSymbols.symb_);
            var_ = var_.op(nops(var_)-1);
            if (is_a<numeric>(var_))
            {
                if (var_.info(info_flags::real) && var_ < _ex0 )
                    return -e.subs(e.op(0) == -e.op(0), subs_options::algebraic).map(*this);
                else if (imag_part(var_) < _ex0)
                    return -e.subs(e.op(0) == -e.op(0), subs_options::algebraic).map(*this);

            }
        }
        else if (is_ex_the_function(e, cos) || is_ex_the_function(e, sec)||
                 is_ex_the_function(e, cosh) || is_ex_the_function(e, sech))
        {
            var_ = collect_common_factors(e.op(0)*externSymbols.symb_);
            var_ = var_.op(nops(var_)-1);
            if (is_a<numeric>(var_))
            {
                if (var_.info(info_flags::real) && var_ < _ex0 )
                    return e.subs(e.op(0) == -e.op(0), subs_options::algebraic).map(*this);
                else if (imag_part(var_) < _ex0)
                    return e.subs(e.op(0) == -e.op(0), subs_options::algebraic).map(*this);

            }
        }

        return e.map(*this);
    }

    ////////////                      simplifyc            //////////////
    simplifyc Simplify;
    Collect_common_factorsc Collect_common_factors;
    numSimplify numSimplifye;
    arguSimplify arguSimplifye;
    expandinv expandinve;
    fracPowBasSubs fracPowBasSubsE;
    funcSubs funcSubsE;
    someMoreSimpRules someMoreSimpRulesE;

    ex Collect_common_factor(const ex& e)
    {
        return collect_common_factors(Collect_common_factors.expr_visitor(e));
    }

    int simplifyc::SetRules(unsigned int m)
    {
        if(m == simplify_options::AlgSimp)
        {
            AlgSimpRules1[pow(wild(2), wild(0)+wild(1))] = pow(wild(2),wild(0))*pow(wild(2),wild(1));
            AlgSimpRules1[wild(3)*pow(wild(2), wild(0)+wild(1))] = wild(3)*pow(wild(2),wild(0))*pow(wild(2),wild(1));
            AlgSimpRules1[pow(wild(1),wild(2)-wild(4))] = pow(wild(1),wild(2))/pow(wild(1),wild(4));
            AlgSimpRules1[wild(3)*pow(wild(1),wild(2)-wild(4))] = wild(3)*pow(wild(1),wild(2))/pow(wild(1),wild(4));
            AlgSimpRules1[pow(wild(1),wild(2)-1)] = pow(wild(1),wild(2))/wild(1);
            AlgSimpRules1[pow(wild(2), _ex1+wild(1))] = wild(2)*pow(wild(2),wild(1));
            AlgSimpRules1[wild(3)*pow(wild(2), _ex1+wild(1))] = wild(3)*wild(2)*pow(wild(2),wild(1));

            //AlgSimpRules2[pow(0,wild(0))] = 0;
            AlgSimpRules2[pow(wild(2),wild(0))*pow(wild(2),wild(1))] = pow(wild(2), wild(0)+wild(1));
            AlgSimpRules2[wild(3)*pow(wild(2),wild(0))*pow(wild(2),wild(1))] = wild(3)*pow(wild(2), wild(0)+wild(1));
            AlgSimpRules2[pow(wild(1),wild(2))/pow(wild(1),wild(4))] = pow(wild(1),wild(2)-wild(4));
            AlgSimpRules2[wild(3)*pow(wild(1),wild(2))/pow(wild(1),wild(4))] = wild(3)*pow(wild(1),wild(2)-wild(4));
            AlgSimpRules2[pow(wild(1),wild(2))/wild(1)] = pow(wild(1),wild(2)-_ex1);
            AlgSimpRules2[wild(3)*pow(wild(1),wild(2))/wild(1)] = wild(3)*pow(wild(1),wild(2)-_ex1);
            AlgSimpRules2[wild(2)*pow(wild(2),wild(1))] = pow(wild(2), _ex1+wild(1));

//            AlgSimpRules2[exp(wild(0))*exp(wild(1))] = exp(wild(0)+wild(1));
//            AlgSimpRules2[wild(2)*exp(wild(0))*exp(wild(1))] = wild(2)*exp(wild(0)+wild(1));
//            AlgSimpRules2[pow(exp(wild(0)),wild(1))] = exp(wild(0)*wild(1));
//            AlgSimpRules2[wild(2)*pow(exp(wild(0)),wild(1))] = wild(2)*exp(wild(0)*wild(1));

            return 0;
        }

//        else if(m == simplify_options::AlgSimp2)
//        {
//            //AlgSimpRules3[pow(0,wild(0))] = 0;
//            AlgSimpRules3[pow(wild(2),wild(0))*pow(wild(2),wild(1))] = pow(wild(2), wild(0)+wild(1));
//            AlgSimpRules3[wild(3)*pow(wild(2),wild(0))*pow(wild(2),wild(1))] = wild(3)*pow(wild(2), wild(0)+wild(1));

//            return 0;
//        }


        else if (m == simplify_options::TrigSimp)
        {
            //sinA^2+cosA^2
            TrigSimpRules1[pow(sin(wild(0)),2)+pow(cos(wild(0)),2)] = _ex1;
            TrigSimpRules1[wild(1)*pow(sin(wild(0)),2)+wild(1)*pow(cos(wild(0)),2)] = wild(1);
            TrigSimpRules1[wild(1)*pow(sin(wild(0)),2)+wild(1)*pow(cos(wild(0)),2)+wild(2)] = wild(1)+wild(2);
            TrigSimpRules1[pow(sin(wild(0)),2)+pow(cos(wild(0)),2)+wild(2)] = _ex1+wild(2);
            //1-cosA^2
            TrigSimpRules1[_ex1 - pow(cos(wild(0)),2)] = pow(sin(wild(0)),2);
            TrigSimpRules1[_ex1 - pow(cos(wild(0)),2)+wild(1)] = pow(sin(wild(0)),2)+wild(1);
            TrigSimpRules1[_ex_1 + pow(cos(wild(0)),2)] = -pow(sin(wild(0)),2);
            TrigSimpRules1[_ex_1 + pow(cos(wild(0)),2)+wild(1)] = -pow(sin(wild(0)),2)+wild(1);
            //1-sinA^2
            TrigSimpRules1[_ex1 - pow(sin(wild(0)),2)] = pow(cos(wild(0)),2);
            TrigSimpRules1[_ex1 - pow(sin(wild(0)),2)+wild(1)] = pow(cos(wild(0)),2)+wild(1);
            TrigSimpRules1[_ex_1 + pow(sin(wild(0)),2)] = -pow(cos(wild(0)),2);
            TrigSimpRules1[_ex_1 + pow(sin(wild(0)),2)+wild(1)] = -pow(cos(wild(0)),2)+wild(1);

            //secA^2-tanA^2
            TrigSimpRules1[wild(2)*pow(sec(wild(0)),2)+ wild(1)*pow(tan(wild(0)),2)] = wild(2)*(pow(sec(wild(0)),2))+ wild(1)*(pow(sec(wild(0)),2)-1);
            TrigSimpRules1[wild(2)*pow(sec(wild(0)),2)+ wild(1)*pow(tan(wild(0)),2)+wild(3)] = wild(2)*(pow(sec(wild(0)),2))+ wild(1)*(pow(sec(wild(0)),2)-1)+wild(3);
            TrigSimpRules1[wild(2)*pow(sec(wild(0)),2)+ pow(tan(wild(0)),2)] = wild(2)*(pow(sec(wild(0)),2))+ (pow(sec(wild(0)),2)-1);
            TrigSimpRules1[wild(2)*pow(sec(wild(0)),2)+ pow(tan(wild(0)),2)+wild(3)] = wild(2)*(pow(sec(wild(0)),2))+ (pow(sec(wild(0)),2)-1)+wild(3);
            TrigSimpRules1[pow(sec(wild(0)),2)+ wild(1)*pow(tan(wild(0)),2)] = pow(sec(wild(0)),2)+ wild(1)*(pow(sec(wild(0)),2)-1);
            TrigSimpRules1[pow(sec(wild(0)),2)+ wild(1)*pow(tan(wild(0)),2)+wild(3)] = pow(sec(wild(0)),2)+ wild(1)*(pow(sec(wild(0)),2)-1)+wild(3);
            //1+tanA^2
            TrigSimpRules1[_ex1 + pow(tan(wild(0)),2)] =pow(sec(wild(0)),2);
            TrigSimpRules1[_ex1 + pow(tan(wild(0)),2)+wild(1)] =pow(sec(wild(0)),2)+wild(1);
            TrigSimpRules1[_ex_1 - pow(tan(wild(0)),2)] =-pow(sec(wild(0)),2);
            TrigSimpRules1[_ex_1 - pow(tan(wild(0)),2)+wild(1)] =-pow(sec(wild(0)),2)+wild(1);
            //secA^2-1
            TrigSimpRules1[_ex1 - pow(sec(wild(0)),2)] =-pow(tan(wild(0)),2);
            TrigSimpRules1[_ex1 - pow(sec(wild(0)),2)+wild(1)] =-pow(tan(wild(0)),2)+wild(1);
            TrigSimpRules1[_ex_1 + pow(sec(wild(0)),2)] =pow(tan(wild(0)),2);
            TrigSimpRules1[_ex_1 + pow(sec(wild(0)),2)+wild(1)] =pow(tan(wild(0)),2)+wild(1);

            //cscA^2-cotA^2
            TrigSimpRules1[wild(2)*pow(csc(wild(0)),2)+ wild(1)*pow(cot(wild(0)),2)] = wild(2)*(pow(csc(wild(0)),2))+ wild(1)*(pow(csc(wild(0)),2)-1);
            TrigSimpRules1[wild(2)*pow(csc(wild(0)),2)+ wild(1)*pow(cot(wild(0)),2)+wild(3)] = wild(2)*(pow(csc(wild(0)),2))+ wild(1)*(pow(csc(wild(0)),2)-1)+wild(3);
            TrigSimpRules1[wild(2)*pow(csc(wild(0)),2)+ pow(cot(wild(0)),2)] = wild(2)*(pow(csc(wild(0)),2))+ (pow(csc(wild(0)),2)-1);
            TrigSimpRules1[wild(2)*pow(csc(wild(0)),2)+ pow(cot(wild(0)),2)+wild(3)] = wild(2)*(pow(csc(wild(0)),2))+ (pow(csc(wild(0)),2)-1)+wild(3);
            TrigSimpRules1[pow(csc(wild(0)),2)+ wild(1)*pow(cot(wild(0)),2)] = pow(csc(wild(0)),2)+ wild(1)*(pow(csc(wild(0)),2)-1);
            TrigSimpRules1[pow(csc(wild(0)),2)+ wild(1)*pow(cot(wild(0)),2)+wild(3)] = pow(csc(wild(0)),2)+ wild(1)*(pow(csc(wild(0)),2)-1)+wild(3);
            //1+cotA^2
            TrigSimpRules1[_ex1 + pow(cot(wild(0)),2)] =pow(csc(wild(0)),2);
            TrigSimpRules1[_ex1 + pow(cot(wild(0)),2)+wild(1)] =pow(csc(wild(0)),2)+wild(1);
            TrigSimpRules1[_ex_1 - pow(cot(wild(0)),2)] =-pow(csc(wild(0)),2);
            TrigSimpRules1[_ex_1 - pow(cot(wild(0)),2)+wild(1)] =-pow(csc(wild(0)),2)+wild(1);
            //cscA^2-1
            TrigSimpRules1[_ex1 - pow(csc(wild(0)),2)] =-pow(cot(wild(0)),2);
            TrigSimpRules1[_ex1 - pow(csc(wild(0)),2)+wild(1)] =-pow(cot(wild(0)),2)+wild(1);
            TrigSimpRules1[_ex_1 + pow(csc(wild(0)),2)] =pow(cot(wild(0)),2);
            TrigSimpRules1[_ex_1 + pow(csc(wild(0)),2)+wild(1)] =pow(cot(wild(0)),2)+wild(1);

            TrigSimpRules2[tan(wild(0))*cos(wild(0))]=sin(wild(0));
            TrigSimpRules2[tan(wild(0))*csc(wild(0))]=sec(wild(0));
            TrigSimpRules2[cot(wild(0))*sin(wild(0))]=cos(wild(0));
            TrigSimpRules2[cot(wild(0))*sec(wild(0))]=csc(wild(0));
            TrigSimpRules2[sec(wild(0))*cos(wild(0))]=_ex1;
            TrigSimpRules2[csc(wild(0))*sin(wild(0))]=_ex1;
            TrigSimpRules2[tan(wild(0))*cot(wild(0))]=_ex1;
            TrigSimpRules2[sin(wild(0))*sec(wild(0))]=tan(wild(0));
            TrigSimpRules2[cos(wild(0))*csc(wild(0))]=cot(wild(0));
            TrigSimpRules2[1/sin(wild(0))] = csc(wild(0));
            TrigSimpRules2[1/cos(wild(0))] = sec(wild(0));
            TrigSimpRules2[1/tan(wild(0))] = cot(wild(0));

//            TrigSimpRules2[tan(wild(0))] = sin(wild(0))/cos(wild(0));
//            TrigSimpRules2[cot(wild(0))] = cos(wild(0))/sin(wild(0));
//            TrigSimpRules2[csc(wild(0))] = 1/sin(wild(0));
//            TrigSimpRules2[sec(wild(0))] = 1/cos(wild(0));

            TrigSimpRules2[sin(wild(0))*cos(wild(1))] = _ex1_2*(sin(wild(0)-wild(1))+sin(wild(0)+wild(1)));//sinA*cosB
            TrigSimpRules2[sin(wild(0))*sin(wild(1))] = _ex1_2*(cos(wild(0)-wild(1))-cos(wild(0)+wild(1)));//sinA*sinB
            TrigSimpRules2[cos(wild(0))*cos(wild(1))] = _ex1_2*(cos(wild(0)-wild(1))+cos(wild(0)+wild(1)));//cosA*cosB

            //cosA^2-sinA^2
            TrigSimpRules2[wild(1)*pow(cos(wild(0)),2)+wild(2)*pow(sin(wild(0)),2)] = (wild(1)+wild(2))/2+_ex1_2*wild(1)*(cos(2*wild(0)))
                                                                                              +_ex1_2*wild(2)*(-cos(2*wild(0)));
            TrigSimpRules2[wild(1)*pow(cos(wild(0)),2)+wild(2)*pow(sin(wild(0)),2)+wild(3)] = (wild(1)+wild(2))/2+_ex1_2*wild(1)*(cos(2*wild(0)))
                                                                                                        +_ex1_2*wild(2)*(-cos(2*wild(0)))+wild(3);
            TrigSimpRules2[wild(1)*pow(cos(wild(0)),2)+pow(sin(wild(0)),2)] = (wild(1)+1)/2+_ex1_2*wild(1)*(cos(2*wild(0)))
                                                                                              +_ex1_2*(-cos(2*wild(0)));
            TrigSimpRules2[wild(1)*pow(cos(wild(0)),2)+pow(sin(wild(0)),2)+wild(3)] = (wild(1)+1)/2+_ex1_2*wild(1)*(cos(2*wild(0)))
                                                                                    +_ex1_2*(-cos(2*wild(0)))+wild(3);

            TrigSimpRules2[pow(cos(wild(0)),2)+wild(2)*pow(sin(wild(0)),2)] = (1+wild(2))/2+_ex1_2*(cos(2*wild(0)))
                                                                                              +_ex1_2*wild(2)*(-cos(2*wild(0)));
            TrigSimpRules2[pow(cos(wild(0)),2)+wild(2)*pow(sin(wild(0)),2)+wild(3)] = (1+wild(2))/2+_ex1_2*(cos(2*wild(0)))
                                                                                                        +_ex1_2*wild(2)*(-cos(2*wild(0)))+wild(3);


//            TrigSimpRules2[sin(-wild(0)*wild(1))] = -sin(wild(0)*wild(1));
//            TrigSimpRules2[cos(-wild(0)*wild(1))] = cos(wild(0)*wild(1));

            return 0;
        }
        else if (m == simplify_options::TrigCombine)
        {
//            TrigCombineRules[wild(1)*pow(sin(wild(0)),2)] = wild(1) - wild(1)*pow(cos(wild(0)),2);
            TrigCombineRules[pow(sin(wild(0)),2)] = _ex1 - pow(cos(wild(0)),2);
//            TrigCombineRules[wild(1)*pow(sec(wild(0)),2)] =wild(1) + wild(1)*pow(tan(wild(0)),2);
            TrigCombineRules[pow(sec(wild(0)),2)] =_ex1 + pow(tan(wild(0)),2);
//            TrigCombineRules[wild(1)*pow(csc(wild(0)),2)] = wild(1) + wild(1)*pow(cot(wild(0)),2);
            TrigCombineRules[pow(csc(wild(0)),2)] = _ex1 + pow(cot(wild(0)),2);

            TrigCombineRules[sin(wild(0))*cos(wild(1))] = _ex1_2*(sin(wild(0)-wild(1))+sin(wild(0)+wild(1)));
            TrigCombineRules[sin(wild(0))*sin(wild(1))] = _ex1_2*(cos(wild(0)-wild(1))-cos(wild(0)+wild(1)));
            TrigCombineRules[pow(sin(wild(0)),2)] = _ex1_2*(1-cos(2*wild(0)));
            TrigCombineRules[cos(wild(0))*cos(wild(1))] = _ex1_2*(cos(wild(0)-wild(1))+cos(wild(0)+wild(1)));
            TrigCombineRules[pow(cos(wild(0)),2)] = _ex1_2*(1+cos(2*wild(0)));
            //TrigCombineRules[sin(-wild(0)*wild(1))] = -sin(wild(0)*wild(1));
            //TrigCombineRules[cos(-wild(0)*wild(1))] = cos(wild(0)*wild(1));

            return 0;
        }
        else if (m == simplify_options::HyperSimp)
        {
            //sechA^2+tanhA^2
            HyperSimpRules1[pow(sech(wild(0)),2)+pow(tanh(wild(0)),2)] = _ex1;
            HyperSimpRules1[wild(1)*pow(sech(wild(0)),2)+wild(1)*pow(tanh(wild(0)),2)] = wild(1);
            HyperSimpRules1[wild(1)*pow(sech(wild(0)),2)+wild(1)*pow(tanh(wild(0)),2)+wild(2)] = wild(1)+wild(2);
            HyperSimpRules1[pow(sech(wild(0)),2)+pow(tanh(wild(0)),2)+wild(2)] = _ex1+wild(2);
            //1-tanhA^2
            HyperSimpRules1[_ex1 - pow(tanh(wild(0)),2)] = pow(sech(wild(0)),2);
            HyperSimpRules1[_ex1 - pow(tanh(wild(0)),2)+wild(1)] = pow(sech(wild(0)),2)+wild(1);
            HyperSimpRules1[_ex_1 + pow(tanh(wild(0)),2)] = -pow(sech(wild(0)),2);
            HyperSimpRules1[_ex_1 + pow(tanh(wild(0)),2)+wild(1)] = -pow(sech(wild(0)),2)+wild(1);
            //1-sechA^2
            HyperSimpRules1[_ex1 - pow(sech(wild(0)),2)] = pow(tanh(wild(0)),2);
            HyperSimpRules1[_ex1 - pow(sech(wild(0)),2)+wild(1)] = pow(tanh(wild(0)),2)+wild(1);
            HyperSimpRules1[_ex_1 + pow(sin(wild(0)),2)] = -pow(tanh(wild(0)),2);
            HyperSimpRules1[_ex_1 + pow(sech(wild(0)),2)+wild(1)] = -pow(tanh(wild(0)),2)+wild(1);

            //cothA^2-cschA^2
            HyperSimpRules1[wild(2)*pow(coth(wild(0)),2)+ wild(1)*pow(csch(wild(0)),2)] = wild(2)*(pow(coth(wild(0)),2))+ wild(1)*(pow(coth(wild(0)),2)-1);
            HyperSimpRules1[wild(2)*pow(coth(wild(0)),2)+ wild(1)*pow(csch(wild(0)),2)+wild(3)] = wild(2)*(pow(coth(wild(0)),2))+ wild(1)*(pow(coth(wild(0)),2)-1)+wild(3);
            HyperSimpRules1[wild(2)*pow(coth(wild(0)),2)+ pow(csch(wild(0)),2)] = wild(2)*(pow(coth(wild(0)),2))+ (pow(coth(wild(0)),2)-1);
            HyperSimpRules1[wild(2)*pow(coth(wild(0)),2)+ pow(csch(wild(0)),2)+wild(3)] = wild(2)*(pow(coth(wild(0)),2))+ (pow(coth(wild(0)),2)-1)+wild(3);
            HyperSimpRules1[pow(coth(wild(0)),2)+ wild(1)*pow(csch(wild(0)),2)] = pow(coth(wild(0)),2)+ wild(1)*(pow(coth(wild(0)),2)-1);
            HyperSimpRules1[pow(coth(wild(0)),2)+ wild(1)*pow(csch(wild(0)),2)+wild(3)] = pow(coth(wild(0)),2)+ wild(1)*(pow(coth(wild(0)),2)-1)+wild(3);
            //1+cschA^2
            HyperSimpRules1[_ex1 + pow(csch(wild(0)),2)] =pow(coth(wild(0)),2);
            HyperSimpRules1[_ex1 + pow(csch(wild(0)),2)+wild(1)] =pow(coth(wild(0)),2)+wild(1);
            HyperSimpRules1[_ex_1 - pow(csch(wild(0)),2)] =-pow(coth(wild(0)),2);
            HyperSimpRules1[_ex_1 - pow(csch(wild(0)),2)+wild(1)] =-pow(coth(wild(0)),2)+wild(1);
            //cothA^2-1
            HyperSimpRules1[_ex1 - pow(coth(wild(0)),2)] =-pow(csch(wild(0)),2);
            HyperSimpRules1[_ex1 - pow(coth(wild(0)),2)+wild(1)] =-pow(csch(wild(0)),2)+wild(1);
            HyperSimpRules1[_ex_1 + pow(coth(wild(0)),2)] =pow(csch(wild(0)),2);
            HyperSimpRules1[_ex_1 + pow(coth(wild(0)),2)+wild(1)] =pow(csch(wild(0)),2)+wild(1);

            //coshA^2-sinhA^2
            HyperSimpRules1[wild(2)*pow(cosh(wild(0)),2)+ wild(1)*pow(sinh(wild(0)),2)] = wild(2)*(pow(cosh(wild(0)),2))+ wild(1)*(pow(cosh(wild(0)),2)-1);
            HyperSimpRules1[wild(2)*pow(cosh(wild(0)),2)+ wild(1)*pow(sinh(wild(0)),2)+wild(3)] = wild(2)*(pow(cosh(wild(0)),2))+ wild(1)*(pow(cosh(wild(0)),2)-1)+wild(3);
            HyperSimpRules1[wild(2)*pow(cosh(wild(0)),2)+ pow(sinh(wild(0)),2)] = wild(2)*(pow(cosh(wild(0)),2))+ (pow(cosh(wild(0)),2)-1);
            HyperSimpRules1[wild(2)*pow(cosh(wild(0)),2)+ pow(sinh(wild(0)),2)+wild(3)] = wild(2)*(pow(cosh(wild(0)),2))+ (pow(cosh(wild(0)),2)-1)+wild(3);
            HyperSimpRules1[pow(cosh(wild(0)),2)+ wild(1)*pow(sinh(wild(0)),2)] = pow(cosh(wild(0)),2)+ wild(1)*(pow(cosh(wild(0)),2)-1);
            HyperSimpRules1[pow(cosh(wild(0)),2)+ wild(1)*pow(sinh(wild(0)),2)+wild(3)] = pow(cosh(wild(0)),2)+ wild(1)*(pow(cosh(wild(0)),2)-1)+wild(3);
            //1+cotA^2
            HyperSimpRules1[_ex1 + pow(sinh(wild(0)),2)] =pow(cosh(wild(0)),2);
            HyperSimpRules1[_ex1 + pow(sinh(wild(0)),2)+wild(1)] =pow(cosh(wild(0)),2)+wild(1);
            HyperSimpRules1[_ex_1 - pow(sinh(wild(0)),2)] =-pow(cosh(wild(0)),2);
            HyperSimpRules1[_ex_1 - pow(sinh(wild(0)),2)+wild(1)] =-pow(cosh(wild(0)),2)+wild(1);
            //cscA^2-1
            HyperSimpRules1[_ex1 - pow(cosh(wild(0)),2)] =-pow(sinh(wild(0)),2);
            HyperSimpRules1[_ex1 - pow(cosh(wild(0)),2)+wild(1)] =-pow(sinh(wild(0)),2)+wild(1);
            HyperSimpRules1[_ex_1 + pow(cosh(wild(0)),2)] =pow(sinh(wild(0)),2);
            HyperSimpRules1[_ex_1 + pow(cosh(wild(0)),2)+wild(1)] =pow(sinh(wild(0)),2)+wild(1);

            HyperSimpRules2[tanh(wild(0))*cosh(wild(0))]=sinh(wild(0));
            HyperSimpRules2[tanh(wild(0))*csch(wild(0))]=sech(wild(0));
            HyperSimpRules2[coth(wild(0))*sinh(wild(0))]=cosh(wild(0));
            HyperSimpRules2[coth(wild(0))*sech(wild(0))]=csch(wild(0));
            HyperSimpRules2[sech(wild(0))*cosh(wild(0))]=_ex1;
            HyperSimpRules2[csch(wild(0))*sinh(wild(0))]=_ex1;
            HyperSimpRules2[tanh(wild(0))*coth(wild(0))]=_ex1;
            HyperSimpRules2[sinh(wild(0))*sech(wild(0))]=tanh(wild(0));
            HyperSimpRules2[cosh(wild(0))*csch(wild(0))]=coth(wild(0));
            HyperSimpRules2[1/sinh(wild(0))] = csch(wild(0));
            HyperSimpRules2[1/cosh(wild(0))] = sech(wild(0));
            HyperSimpRules2[1/tanh(wild(0))] = coth(wild(0));
//            HyperSimpRules2[tanh(wild(0))] = sinh(wild(0))/cosh(wild(0));
//            HyperSimpRules2[coth(wild(0))] = cosh(wild(0))/sinh(wild(0));
//            HyperSimpRules2[csch(wild(0))] = 1/sinh(wild(0));
//            HyperSimpRules2[sech(wild(0))] = 1/cosh(wild(0));


            HyperSimpRules2[sinh(wild(0))*cosh(wild(1))] = _ex1_2*(sinh(wild(0)-wild(1))+sinh(wild(0)+wild(1)));//sinhA*coshB
            HyperSimpRules2[sinh(wild(0))*sinh(wild(1))] = _ex1_2*(-cosh(wild(0)-wild(1))+cosh(wild(0)+wild(1)));//sinhA*sinhB
            HyperSimpRules2[cosh(wild(0))*cosh(wild(1))] = _ex1_2*(cosh(wild(0)-wild(1))+cosh(wild(0)+wild(1)));//coshA*coshB

            //coshA^2+sinhA^2=cosh2A
            HyperSimpRules2[wild(1)*pow(cosh(wild(0)),2)+wild(2)*pow(sinh(wild(0)),2)] = (wild(1)-wild(2))/2+_ex1_2*wild(1)*(cosh(2*wild(0)))
                                                                                              +_ex1_2*wild(2)*(cosh(2*wild(0)));
            HyperSimpRules2[wild(1)*pow(cosh(wild(0)),2)+wild(2)*pow(sinh(wild(0)),2)+wild(3)] = (wild(1)-wild(2))/2+_ex1_2*wild(1)*(cosh(2*wild(0)))
                                                                                                        +_ex1_2*wild(2)*(cosh(2*wild(0)))+wild(3);
            HyperSimpRules2[wild(1)*pow(cosh(wild(0)),2)+pow(sinh(wild(0)),2)] = (wild(1)-1)/2+_ex1_2*wild(1)*(cosh(2*wild(0)))
                                                                                    +_ex1_2*(cosh(2*wild(0)));
            HyperSimpRules2[wild(1)*pow(cosh(wild(0)),2)+pow(sinh(wild(0)),2)+wild(3)] = (wild(1)-1)/2+_ex1_2*wild(1)*(cosh(2*wild(0)))
                                                                                              +_ex1_2*(cosh(2*wild(0)))+wild(3);

            HyperSimpRules2[pow(cosh(wild(0)),2)+wild(2)*pow(sinh(wild(0)),2)] = (1-wild(2))/2+_ex1_2*(cosh(2*wild(0)))
                                                                                    +_ex1_2*wild(2)*(cosh(2*wild(0)));
            HyperSimpRules2[pow(cosh(wild(0)),2)+wild(2)*pow(sinh(wild(0)),2)+wild(3)] = (1-wild(2))/2+_ex1_2*(cosh(2*wild(0)))
                                                                                              +_ex1_2*wild(2)*(cosh(2*wild(0)))+wild(3);

            return 0;
        }
        else if (m == simplify_options::HyperCombine)
        {
//            HyperCombineRules[wild(1)*pow(sinh(wild(0)),2)] = wild(1)*pow(cosh(wild(0)),2)-wild(1);
            HyperCombineRules[pow(sinh(wild(0)),2)] = pow(cosh(wild(0)),2)-_ex1;
//            HyperCombineRules[wild(1)*pow(sech(wild(0)),2)] =wild(1) - wild(1)*pow(tanh(wild(0)),2);
            HyperCombineRules[pow(sech(wild(0)),2)] =_ex1 - pow(tanh(wild(0)),2);
//            HyperCombineRules[wild(1)*pow(csch(wild(0)),2)] = wild(1)*pow(coth(wild(0)),2)- wild(1);
            HyperCombineRules[pow(csch(wild(0)),2)] = pow(coth(wild(0)),2)-_ex1;

            HyperCombineRules[sinh(wild(0))*cosh(wild(1))] = _ex1_2*(sinh(wild(0)-wild(1))+sinh(wild(0)+wild(1)));
            HyperCombineRules[sinh(wild(0))*sinh(wild(1))] = _ex1_2*(-cosh(wild(0)-wild(1))+cosh(wild(0)+wild(1)));
            HyperCombineRules[cosh(wild(0))*cosh(wild(1))] = _ex1_2*(cosh(wild(0)-wild(1))+cosh(wild(0)+wild(1)));
            HyperCombineRules[pow(sinh(wild(0)),2)] = _ex1_2*(-1+cosh(2*wild(0)));
            HyperCombineRules[pow(cosh(wild(0)),2)] = _ex1_2*(1+cosh(2*wild(0)));
            //HyperCombineRules[sinh(-wild(0)*wild(1))] = -sinh(wild(0)*wild(1));
            //HyperCombineRules[cosh(-wild(0)*wild(1))] = cosh(wild(0)*wild(1));

            return 0;
        }

        else if (m == simplify_options::logSimp)
        {
            //rules = logSimp;
            logSimpRules[log(pow(wild(0), wild(1)))] = wild(1)*log(wild(0));
            logSimpRules[log(wild(0)*wild(1))] = log(wild(0)) + log(wild(1));
            logSimpRules[log(exp(_ex1))] = _ex1;
        }
        else if (m == simplify_options::JacobiSimp)
        {
            //rules = JacobiSimp;
            JacobiSimpRules1[pow(JacobiCN(wild(0),wild(1)),_ex2)] = _ex1-pow(JacobiSN(wild(0),wild(1)),_ex2);
            JacobiSimpRules1[pow(JacobiDN(wild(0),wild(1)),_ex2)] = _ex1-wild(1)*wild(1)*pow(JacobiSN(wild(0),wild(1)),_ex2);

            JacobiSimpRules2[JacobiNS(wild(0),wild(1))] = 1/JacobiSN(wild(0),wild(1));
            JacobiSimpRules2[JacobiNC(wild(0),wild(1))] = 1/JacobiCN(wild(0),wild(1));
            JacobiSimpRules2[JacobiND(wild(0),wild(1))] = 1/JacobiDN(wild(0),wild(1));
            JacobiSimpRules2[JacobiSC(wild(0),wild(1))] = JacobiSN(wild(0),wild(1))/JacobiCN(wild(0),wild(1));
            JacobiSimpRules2[JacobiSD(wild(0),wild(1))] = JacobiSN(wild(0),wild(1))/JacobiDN(wild(0),wild(1));
            JacobiSimpRules2[JacobiCS(wild(0),wild(1))] = JacobiCN(wild(0),wild(1))/JacobiSN(wild(0),wild(1));
            JacobiSimpRules2[JacobiDS(wild(0),wild(1))] = JacobiDN(wild(0),wild(1))/JacobiSN(wild(0),wild(1));

        }
        return 0;
    }

    ex simplifyc::algSimp(const ex& e)
    {
        ex y=(e);
        this->SetRules(simplify_options::AlgSimp);
        TrigArgSign_Complx trigarg;
        ex xprev;
        do
        {
            xprev = y;
            y = y.subs(AlgSimpRules1/*, subs_options::algebraic*/);
        } while(xprev != y);
        do
        {
            xprev = y;
            y = y.subs(AlgSimpRules2/*, subs_options::algebraic*/);
            y = y.subs((lst){wild(2)*pow(wild(2),wild(1)) == pow(wild(2), _ex1+wild(1))}/*,subs_options::algebraic*/); //we apply this rule separately to increase speed.
            y = trigarg.expr_visitor(y);
            numSimplifye.primefactrs.clear();
            y=(numSimplifye.expr_visitor(y));
        } while(xprev != y);

        ex numericbaseexp;
        //handling 2^x*3^x->(2*3)^x,2^x*e^x->(2*e)^x,
        exmap matched;
        do {
            xprev = y;
            //            std::cout<<y<<std::endl;
            for (const_preorder_iterator i = xprev.preorder_begin(); i!=xprev.preorder_end(); ++i) {
                if (is_a<mul>(*i)) {
                    matched.clear();
                    numericbaseexp=_ex1;

                    for (int j = 0; j < nops(*i); ++j) {
                        if ((is_a<power>((*i).op(j)) and is_number((*i).op(j).op(0)))
                            or is_ex_the_function((*i).op(j),exp)) {
                            numericbaseexp *= (*i).op(j);
                        }
                    }

                    if (numericbaseexp.nops()>1) {
                        if ((numericbaseexp).match(power(wild(0),wild(1))*power(wild(2),wild(1)),matched)) {
                            y=y.subs(power(matched[wild(0)],matched[wild(1)])*power(matched[wild(2)],matched[wild(1)])
                                       ==power(matched[wild(0)]*matched[wild(2)],matched[wild(1)]));
                            y=y.subs(wild(4)*power(matched[wild(0)],matched[wild(1)])*power(matched[wild(2)],matched[wild(1)])
                                       ==wild(4)*power(matched[wild(0)]*matched[wild(2)],matched[wild(1)]));
                        }
                        else if ((numericbaseexp).match(wild(3)*power(wild(0),wild(1))*power(wild(2),wild(1)),matched)) {
                            y=y.subs(matched[wild(3)]*power(matched[wild(0)],matched[wild(1)])*power(matched[wild(2)],matched[wild(1)])
                                       ==matched[wild(3)]*power(matched[wild(0)]*matched[wild(2)],matched[wild(1)]));
                            y=y.subs(wild(4)*matched[wild(3)]*power(matched[wild(0)],matched[wild(1)])*power(matched[wild(2)],matched[wild(1)])
                                       ==wild(4)*matched[wild(3)]*power(matched[wild(0)]*matched[wild(2)],matched[wild(1)]));
                        }


                        else if ((numericbaseexp).match(power(wild(0),wild(1))*exp(-wild(1)),matched)) {
                            y=y.subs(power(matched[wild(0)],matched[wild(1)])*exp(-matched[wild(1)])
                                       ==power(matched[wild(0)]*exp(_ex_1),matched[wild(1)]));
                            y=y.subs(wild(4)*power(matched[wild(0)],matched[wild(1)])*exp(-matched[wild(1)])
                                       ==wild(4)*power(matched[wild(0)]*exp(_ex_1),matched[wild(1)]));
                        }
                        else if ((numericbaseexp).match(wild(2)*power(wild(0),wild(1))*exp(-wild(1)),matched)) {
                            y=y.subs(wild(2)*power(matched[wild(0)],matched[wild(1)])*exp(-matched[wild(1)])
                                       ==wild(2)*power(matched[wild(0)]*exp(_ex_1),matched[wild(1)]));
                        }


                        else if ((numericbaseexp).match(power(wild(0),wild(1))*exp(wild(1)),matched)
                                 || (*i).match(wild(2)*power(wild(0),wild(1))*exp(wild(1)),matched)) {
                            y=y.subs(power(matched[wild(0)],matched[wild(1)])*exp(matched[wild(1)])
                                       ==power(matched[wild(0)]*exp(_ex1),matched[wild(1)]));
                            y=y.subs(wild(4)*power(matched[wild(0)],matched[wild(1)])*exp(matched[wild(1)])
                                       ==wild(4)*power(matched[wild(0)]*exp(_ex1),matched[wild(1)]));
                        }
                        else if ((numericbaseexp).match(wild(2)*power(wild(0),wild(1))*exp(wild(1)),matched)) {
                            y=y.subs(matched[wild(2)]*power(matched[wild(0)],matched[wild(1)])*exp(matched[wild(1)])
                                       ==matched[wild(2)]*power(matched[wild(0)]*exp(_ex1),matched[wild(1)]));
                            y=y.subs(wild(4)*matched[wild(2)]*power(matched[wild(0)],matched[wild(1)])*exp(matched[wild(1)])
                                       ==wild(4)*matched[wild(2)]*power(matched[wild(0)]*exp(_ex1),matched[wild(1)]));

                        }

                    }

                }
            }

        } while (xprev!=y);
        return y;
    }

    ex simplifyc::operator()(const ex& e, const unsigned int& rules)
    {
        if(e.has(Infinity) || e.has(-Infinity)
            || is_a<Diff>(e) || is_a<Integrate>(e) || is_a<Limit>(e)) return e;
        ex y=(e);

//std::cout<<y<<std::endl;
        if (rules == simplify_options::AlgSimp)
        {

            return algSimp(y);
        }
        else if (rules == simplify_options::FuncSimp)
        {
            y = algSimp(y);
            ex xprev;
            this->SetRules(simplify_options::TrigSimp);
            do
            {
                xprev = y;
                y = (y.subs(TrigSimpRules1));
            } while(xprev != y);
            do
            {
                xprev = y;
                y = (y.subs(TrigSimpRules2));
            } while(xprev != y);
            this->SetRules(simplify_options::HyperSimp);
            do
            {
                xprev = y;
                y = (y.subs(HyperSimpRules1)/*,subs_options::algebraic*/);
            } while(xprev != y);
            do
            {
                xprev = y;
                y = (y.subs(HyperSimpRules2)/*,subs_options::algebraic*/);
            } while(xprev != y);

//            this->SetRules(simplify_options::JacobiSimp);
//            do
//            {
//                xprev = y;
//                y = (y.subs(JacobiSimpRules2, subs_options::algebraic));
//            } while(xprev != y);
//            do
//            {
//                xprev = y;
//                y = y.subs(JacobiSimpRules1, subs_options::algebraic);
//            } while(xprev != y);


//            this->SetRules(logSimp);
//            do
//            {
//                xprev = y;
//                y = y.subs(logSimpRules, subs_options::algebraic);
//            } while(xprev != y);

            y = algSimp(y);

            return y;
        }


        else if (rules == simplify_options::TrigSimp)
        {
            y = algSimp(y);

            this->SetRules(simplify_options::TrigSimp);
            ex xprev;
            do
            {
                xprev = y;
                y = y.subs(TrigSimpRules1/*, subs_options::algebraic*/);
            } while(xprev != y);
            do
            {
                xprev = y;
                y = y.subs(TrigSimpRules2/*, subs_options::algebraic*/);
            } while(xprev != y);

            y = algSimp(y);
            return y;
        }

        else if (rules == simplify_options::TrigCombine)
        {
            y = algSimp(y);
            this->SetRules(simplify_options::TrigSimp);
            ex xprev;
            do
            {
                xprev = y;
                y = y.subs(TrigSimpRules1/*, subs_options::algebraic*/);
            } while(xprev != y);
            do
            {
                xprev = y;
                y = y.subs(TrigSimpRules2/*, subs_options::algebraic*/);
            } while(xprev != y);
            y = algSimp(y);


            this->SetRules(simplify_options::TrigCombine);
            do
            {
                xprev = y;
                y = y.subs(TrigCombineRules, subs_options::algebraic);//.expand(expand_options::expand_function_args);
            } while(xprev != y);
            y = algSimp(y);

            return y;
        }


        else if (rules == simplify_options::HyperSimp)
        {
            y = algSimp(y);

            this->SetRules(simplify_options::HyperSimp);
            ex xprev;

            do
            {
                xprev = y;
                y = y.subs(HyperSimpRules1);
            } while(xprev != y);
            do
            {
                xprev = y;
                y = y.subs(HyperSimpRules2);
            } while(xprev != y);

            y = algSimp(y);
            return y;
        }

        else if (rules == simplify_options::HyperCombine)
        {
            y = algSimp(y);
            this->SetRules(simplify_options::HyperSimp);
            ex xprev;
            do
            {
                xprev = y;
                y = y.subs(HyperSimpRules1/*, subs_options::algebraic*/);
            } while(xprev != y);
            do
            {
                xprev = y;
                y = y.subs(HyperSimpRules2/*, subs_options::algebraic*/);
            } while(xprev != y);
            y = algSimp(y);


            this->SetRules(simplify_options::HyperCombine);
            do
            {
                xprev = y;
                y = y.subs(HyperCombineRules, subs_options::algebraic);//.expand(expand_options::expand_function_args);
            } while(xprev != y);

            y = algSimp(y);
            return y;
        }

//        else if (rules == logSimp)
//        {
//            y = this->operator()(y,AlgSimp);

//            this->SetRules(logSimp);
//            ex xprev;
//            do
//            {
//                xprev = y;
//                y = y.subs(logSimpRules, subs_options::algebraic).expand(expand_options::expand_function_args);
//            } while(xprev != y);

//            y = this->operator()(y,AlgSimp);
//            return y;
//        }

        return e;
    }

    /// expanding terms containing inverse power
    ex expandinv::expr_visitor(const ex& e)
    {
        if(is_a<mul>(e))
        {
            repls.clear();
            e.match(pow(wild(1), wild(0))*pow(wild(2), wild(0)), repls);
            e.match(wild(3)*pow(wild(1), wild(0))*pow(wild(2), wild(0)), repls);

            if(!repls.empty())
            {
                if((is_a<numeric>(repls[wild(0)]) && ex_to<numeric>(repls[wild(0)]).is_negative()) ||
                    (nops(repls[wild(0)]) > 1 && is_a<numeric>(repls[wild(0)].op(nops(repls[wild(0)]) - 1))
                     && ex_to<numeric>(repls[wild(0)].op(nops(repls[wild(0)]) - 1)).is_negative()))
                {
                    if(repls[wild(3)] == _ex0)
                        return pow(expand(repls[wild(1)]*repls[wild(2)]), repls[wild(0)]);
                    else
                        return repls[wild(3)]*pow(expand(repls[wild(1)]*repls[wild(2)]), repls[wild(0)]);
                }
            }
        }

        return e.map(*this);
    }

    /**doing factors of fractional power bases, function arguments. **/
    ex arguSimplify::expr_visitor(const ex &e)
    {
        return (Simplify(Factor(e))).map(*this);
    }

    /** doing number simplify. **/
    ex numSimplify::getPrimefactors(const ex &e, const ex &fractimes)
    {
        primefactrs=primeFactors(ex_to<numeric>(e));

        if(!primefactrs.empty())
        {
            ex modiExpr=_ex1;
            for(auto itr = primefactrs.begin(); itr!=primefactrs.end();itr++)
            {
                modiExpr=modiExpr*pow(itr->first,itr->second*fractimes);
            }

            return modiExpr;
        }
        else
            return pow(e,fractimes);
    }
    /////////////////////////////////////////////////////////////
    /// (6)^(3/2)=(3*2)^(3/2)=3^(3/2)*2^(3/2)
    ex numSimplify::expr_visitor(const ex& e)
    {
        if(is_a<power>(e)&&is_a<numeric>((e.op(0)))
            &&is_a<numeric>((e.op(1))))
        {
            if( e.op(0).info(info_flags::positive) && e.op(1).info(info_flags::rational)
                &&((numer(e.op(0))<=largstNumsimp&&denom(e.op(0))<=largstNumsimp
                     &&numer(e.op(1))<=largstNumsimp&&denom(e.op(1))<=largstNumsimp)))
            {
                return (numer(e.op(0))==_ex1?_ex1:getPrimefactors(numer(e.op(0)),e.op(1)))/(denom(e.op(0))==_ex1?_ex1:getPrimefactors(denom(e.op(0)),e.op(1)));
            }
            else if(e.op(0).info(info_flags::negative) && e.op(1).info(info_flags::rational))
            {
                if((-numer(e.op(0))<=largstNumsimp&&denom(e.op(0))<=largstNumsimp
                     &&numer(e.op(1))<=largstNumsimp&&denom(e.op(1))<=largstNumsimp))
                {
                    const ex temexpr = (numer(-e.op(0))==_ex1?_ex1:getPrimefactors(numer(-e.op(0)),e.op(1)))/(denom(e.op(0))==_ex1?_ex1:getPrimefactors(denom(e.op(0)),e.op(1)));
                    return (pow(-1,(e.op(1)))*temexpr);
                }
                else
                {
                    return (pow(-1,(e.op(1)))*pow(-e.op(0),e.op(1)));
                }


            }

        }

        return e.map(*this);
    }

    /////////////////////////////////////////////////////////////
    /** replacing the "pow" terms with created symbols, which have less degree than expandLevel and base is in add container.
    It is level 1 implementation of  powBaseSubsLessThanDeg. **/
    ex powBaseSubsLessThanDegLvl_1::expr_visitor(const ex& _e)
    {
        if(is_a<power>(_e) && (is_a<add>(_e.op(0))) && (_e.op(1))>expandLevel)
        {
            if((!exprToSymMap.empty() && exprToSymMap.find(_e.op(0))==exprToSymMap.end())
                ||exprToSymMap.empty())
            {
                j=j+1;

                str = "powBaseSubs0_" + to_string(j);
                expr = generator.symGenerator(str);
                exprToSymMap[_e.op(0)]=expr;
            }

            if(!exprToSymMap.empty() && exprToSymMap.find(_e.op(0))!=exprToSymMap.end())
                return pow(exprToSymMap[_e.op(0)],_e.op(1));
        }

        return _e.map(*this);
    }

    /////////////////////////////////////////////////////////////
    /** It is level 1 implementation of fracPowBasSubs. **/
    ex fracPowBasSubsLvl_1::expr_visitor(const ex& e)
    {
        if(is_a<power>(e)&&denom(e.op(1))!=_ex1)
        {
            numer_denomClt = (e.op(0)).numer_denom();

            tem = Simplify(collect_common_factors(Factor(Simplify(expand(numer_denomClt.op(0)))))/
                           collect_common_factors(Factor(Simplify(expand(numer_denomClt.op(1))))));

            if((!baseCltLvl_1.empty() && baseCltLvl_1.find(tem)==baseCltLvl_1.end())
                || baseCltLvl_1.empty())
            {
                j=j+1;

                str = "genSymbLvl_1_" + to_string(j);
                expr = generator.symGenerator(str);
                baseCltLvl_1[tem]=expr;
            }

            if(!baseCltLvl_1.empty() && baseCltLvl_1.find(tem)!=baseCltLvl_1.end())
                return pow(baseCltLvl_1[tem],(e.op(1)));
        }

        return e.map(*this);
    }

    /////////////////////////////////////////////////////////////
    /** replacing the fractional power terms with created symbols. All type bases are included,
 * such as numeric, symbols, add container. This class has been used in Factor function before factoring.    **/
    ex fracPowBasSubsFactor::expr_visitor(const ex& e)
    {
        if(is_a<power>(e)&&denom(e.op(1))!=_ex1)
        {

            numer_denomClt = (e.op(0)).numer_denom();

            tem = Simplify(collect_common_factors(Factor(Simplify(expand(numer_denomClt.op(0)))))/
                           collect_common_factors(Factor(Simplify(expand(numer_denomClt.op(1))))));

            if((!baseClt.empty() && baseClt.find(tem)==baseClt.end())
                || baseClt.empty())
            {
                j=j+1;

                str = "genSymb1_" + to_string(j);
                expr = generator.symGenerator(str);
                baseClt[tem]=expr;
            }

            if(!baseClt.empty() && baseClt.find(tem)!=baseClt.end())
                return pow(baseClt[tem],(e.op(1)));
        }

        return e.map(*this);
    }

    /////////////////////////////////////////////////////////////
    /** replacing the "pow" terms with created symbols, which have degree less than expandLevel and base is in add container. **/
    ex powBaseSubsLessThanDeg::expr_visitor(const ex& _e)
    {
        if(is_a<power>(_e) && (is_a<add>(_e.op(0))) && _e.op(1).info(info_flags::integer) &&
            ((_e.op(1))>expandLevel||(-_e.op(1))>expandLevel))
        {
            Lvl_1.set();
            numer_denomClt = Lvl_1.expr_visitor(_e.op(0)).numer_denom();

            tem = Simplify(collect_common_factors(Factor(Simplify(expand(numer_denomClt.op(0)))))/
                           collect_common_factors(Factor(Simplify(expand(numer_denomClt.op(1))))));

            if(!Lvl_1.exprToSymMap.empty())
                tem = Simplify(genSymbSubs(tem,Lvl_1.exprToSymMap));

            if((!exprToSymMap.empty() && exprToSymMap.find(tem)==exprToSymMap.end())
                ||exprToSymMap.empty())
            {
                j=j+1;

                str = "powBaseSubs2_" + to_string(j);
                expr = generator.symGenerator(str);
                exprToSymMap[tem]=expr;
            }

            if(!exprToSymMap.empty() && exprToSymMap.find(tem)!=exprToSymMap.end())
                return pow(exprToSymMap[tem],_e.op(1));
        }

        return _e.map(*this);
    }



    /** replacing base of fractional power with generated symbols. This simplifies all fractional power with base expressions.  **/
    ex fracPowBasSubs::expr_visitor(const ex& e)
    {
        if(is_a<power>(e)&&denom(e.op(1))!=_ex1)
        {

            numer_denomClt = (e.op(0)).numer_denom();

            tem = Simplify(collect_common_factors(Factor(Simplify(expand(numer_denomClt.op(0)),simplify_options::AlgSimp)))/
                               collect_common_factors(Factor(Simplify(expand(numer_denomClt.op(1)),simplify_options::AlgSimp))),simplify_options::AlgSimp);
            tem=Lvl_1.expr_visitor(tem);
            if(!Lvl_1.baseCltLvl_1.empty())
            {
                ex temtemexpr_;
                for(auto it = Lvl_1.baseCltLvl_1.begin(); it != Lvl_1.baseCltLvl_1.end(); it++) // coefficients of each generated symbol are simplified separately
                {
                    if(tem.is_polynomial((*it).second))
                    {
                        temtemexpr_ = _ex0;
                        for(int i = 0; i <=degree(tem,(*it).second); i++)
                        {
                            numer_denomClt = (tem.coeff((*it).second,i)).numer_denom();
                            temtemexpr_ = temtemexpr_+ pow((*it).second,i)*Simplify((is_a<numeric>(numer_denomClt.op(0))?numer_denomClt.op(0):collect_common_factors((Factor(Simplify((numer_denomClt.op(0)),simplify_options::AlgSimp)))))/
                                                                                            (is_a<numeric>(numer_denomClt.op(1))?numer_denomClt.op(1):collect_common_factors((Factor(Simplify((numer_denomClt.op(1)),simplify_options::AlgSimp))))),simplify_options::AlgSimp);
                        }
                        tem = temtemexpr_;
                    }
                    else
                    {
                        numer_denomClt = tem.numer_denom();
                        tem = Simplify((is_a<numeric>(numer_denomClt.op(0))?numer_denomClt.op(0):collect_common_factors((Factor(Simplify(expand(numer_denomClt.op(0)),simplify_options::AlgSimp)))))/
                                           (is_a<numeric>(numer_denomClt.op(1))?numer_denomClt.op(1):collect_common_factors((Factor(Simplify(expand(numer_denomClt.op(1)),simplify_options::AlgSimp))))),simplify_options::AlgSimp);
                    }
                }

                tem = Simplify(genSymbSubs(tem,Lvl_1.baseCltLvl_1),simplify_options::AlgSimp);
                Lvl_1.set();
            }

            if((!baseClt.empty() && baseClt.find(tem)==baseClt.end())
                || baseClt.empty())
            {
                j=j+1;

                str = "genSymb4_" + to_string(j);
                expr = generator.symGenerator(str);
                baseClt[tem]=expr;
            }

            if(!baseClt.empty() && baseClt.find(tem)!=baseClt.end())
                return pow(baseClt[tem],(e.op(1)));

        }

        return e.map(*this);
    };


    ////////////////////////////////////////////////////////////////
    /** replacing some functions with generated symbols.  **/
    ex funcSubs::expr_visitor(const ex& e)
    {
        if((is_a<function>(e) && !is_ex_the_function(e,exp))
           || is_a<Limit>(e) || is_a<Diff>(e) || is_a<Integrate>(e)
            /*is_ex_the_function(e, sin)||is_ex_the_function(e, cos)||is_ex_the_function(e, tan)||
            is_ex_the_function(e, csc)||is_ex_the_function(e, sec)||is_ex_the_function(e, cot)||
            is_ex_the_function(e, sinh)||is_ex_the_function(e, cosh)||is_ex_the_function(e, tanh)||
            is_ex_the_function(e, csch)||is_ex_the_function(e, sech)||is_ex_the_function(e, coth)||
            is_ex_the_function(e, JacobiSN)||is_ex_the_function(e, JacobiCN)||is_ex_the_function(e, JacobiDN)||
            is_ex_the_function(e, JacobiNS)||is_ex_the_function(e, JacobiNC)||is_ex_the_function(e, JacobiND)||
            is_ex_the_function(e, JacobiSC)||is_ex_the_function(e, JacobiSD)||is_ex_the_function(e, JacobiCS)||
            is_ex_the_function(e, JacobiDS)*/)
        {
            if((!baseClt.empty() && baseClt.find(e)==baseClt.end())
                || baseClt.empty())
            {
                j=j+1;

                str = "funcSymb3_" + to_string(j);
                expr = generator.symGenerator(str);
                baseClt[e]=expr;
            }

            if(!baseClt.empty() && baseClt.find(e)!=baseClt.end())
            {
                return baseClt[e];
            }

        }

        //It handles exponential functions with its exponent.//
        else if(is_ex_the_function(e,exp))
        {
            expr2 = (Collect_common_factors.expr_visitor(e.op(0))).subs(externSymbols.factSymb_==_ex1);

            if(is_a<mul>(expr2) && is_a<numeric>(expr2.op(nops(expr2)-1)))
            {

                expr3 = numer(expr2.op(nops(expr2)-1));
                if((!baseClt.empty() && baseClt.find(exp(expr2/expr3))==baseClt.end())
                    || baseClt.empty())
                {

                    j=j+1;

                    str = "funcSymb3_" + to_string(j);
                    expr = generator.symGenerator(str);
                    baseClt[exp(expr2/expr3)]=expr;
                }

                if(!baseClt.empty() && baseClt.find(exp(expr2/expr3))!=baseClt.end())
                {
                    return pow(baseClt[exp(expr2/expr3)],expr3);
                }

            }
            else
            {
                if((!baseClt.empty() && baseClt.find(exp(expr2))==baseClt.end())
                    || baseClt.empty())
                {

                    j=j+1;

                    str = "funcSymb3_" + to_string(j);
                    expr = generator.symGenerator(str);
                    baseClt[exp(expr2)]=expr;
                }

                if(!baseClt.empty() && baseClt.find(exp(expr2))!=baseClt.end())
                {
                    return (baseClt[exp(expr2)]);
                }
            }
        }
        return e.map(*this);
    }



    ////////////////////////////////////////////////////////////////
    /** Applying the simplification rules  x^(3/2)=x*x^(1/2)**/
    ex someMoreSimpRules::expr_visitor(const ex& e)
    {

        if(is_a<power>(e) && (e.op(1)).info(info_flags::real) && denom(e.op(1)) != _ex1)
        {
            iNum = (int)(ex_to<numeric>(e.op(1))).to_double();
            if(iNum != 0)
                return (pow(e.op(0),iNum)*pow(e.op(0),e.op(1)-iNum*_ex1)).map(*this);
        }

        return (e).map(*this);
    }

    ////////////////////////////////////////////////////////////
    /// This collect common numerical factors inside base of fractional power.
    ///
    ex Collect_common_factorsc::expr_visitor(const ex& _e)
    {
        if(is_a<add>(_e))
            return collect_common_factors(_e).map(*this);
        else if(is_a<power>(_e) and is_a<add>(_e.op(0))
            and is_a<numeric>(_e.op(1)) and _e.op(1).denom()!=_ex1)//base of fractional power
        {
            temex = collect_common_factors(_e.op(0)*externSymbols.factSymb_);
            temex2 = _ex1;
            temex3 = _ex1;

            for (size_t i=0;i<nops(temex);i++)
            {
                if(is_a<numeric>(temex.op(i)))
                    temex2=temex2*temex.op(i);
                else if(temex.op(i) != externSymbols.factSymb_)
                    temex3=temex3*temex.op(i);
            }

            if((temex2)!=_ex1){
                // N.B: don't map when an extra expression (here externSymbols.factSymb_) is included
                // in original expression.
                if(temex2.info(info_flags::positive))
                    return (power(temex2,_e.op(1))*power(temex3,_e.op(1))).map(*this);
                else if(temex2.info(info_flags::negative))
                    return (power(-temex2,_e.op(1))*power(-temex3,_e.op(1))).map(*this); // N.B: don't map when an extra expression (here externSymbols.factSymb_) is included

            }
        }

        return _e.map(*this);
    }

    ////////////////////////////////////////////////////////////

    //ex Simplify2(const ex& expr_)
    //{
    //    exmap AlgSimpRules2;
    //    AlgSimpRules2[pow(pow(F,wild(0)),wild(1))] = pow(F, wild(0)*wild(1));
    //    AlgSimpRules2[pow(pow(F_,wild(0)),wild(1))] = pow(F_, wild(0)*wild(1));
    //    AlgSimpRules2[pow(pow(Fd_,wild(0)),wild(1))] = pow(Fd_, wild(0)*wild(1));
    //    AlgSimpRules2[pow(pow(X_,wild(0)),wild(1))] = pow(X_, wild(0)*wild(1));
    //    AlgSimpRules2[pow(pow(Y_,wild(0)),wild(1))] = pow(Y_, wild(0)*wild(1));

    //    AlgSimpRules2[pow(pow(wild(2)*F,wild(0)),wild(1))] = pow(pow(wild(2),wild(0)),wild(1))*pow(F, wild(0)*wild(1));
    //    AlgSimpRules2[pow(pow(wild(2)*F_,wild(0)),wild(1))] = pow(pow(wild(2),wild(0)),wild(1))*pow(F_, wild(0)*wild(1));
    //    AlgSimpRules2[pow(pow(wild(2)*Fd_,wild(0)),wild(1))] = pow(pow(wild(2),wild(0)),wild(1))*pow(Fd_, wild(0)*wild(1));
    //    AlgSimpRules2[pow(pow(wild(2)*X_,wild(0)),wild(1))] = pow(pow(wild(2),wild(0)),wild(1))*pow(X_, wild(0)*wild(1));
    //    AlgSimpRules2[pow(pow(wild(2)*Y_,wild(0)),wild(1))] = pow(pow(wild(2),wild(0)),wild(1))*pow(Y_, wild(0)*wild(1));

    //    AlgSimpRules2[pow(wild(2)*pow(F,wild(0)),wild(1))] = pow(wild(2),wild(1))*pow(F, wild(0)*wild(1));
    //    AlgSimpRules2[pow(wild(2)*pow(F_,wild(0)),wild(1))] = pow(wild(2),wild(1))*pow(F_, wild(0)*wild(1));
    //    AlgSimpRules2[pow(wild(2)*pow(Fd_,wild(0)),wild(1))] = pow(wild(2),wild(1))*pow(Fd_, wild(0)*wild(1));
    //    AlgSimpRules2[pow(wild(2)*pow(X_,wild(0)),wild(1))] = pow(wild(2),wild(1))*pow(X_, wild(0)*wild(1));
    //    AlgSimpRules2[pow(wild(2)*pow(Y_,wild(0)),wild(1))] = pow(wild(2),wild(1))*pow(Y_, wild(0)*wild(1));


    //    ex xprev,y;
    //    y = expr_;
    //    do
    //    {
    //        xprev = y;
    //        y = y.subs(AlgSimpRules2, subs_options::algebraic);
    //    } while(xprev != y);

    //    return y;
    //}

    ////////////////////////////////////////////////////////////

    ex simplify(const ex& expr_, unsigned int rules)
    {
        if(expr_.has(Infinity) || expr_.has(-Infinity)
            || is_a<Diff>(expr_) || is_a<Integrate>(expr_) || is_a<Limit>(expr_)) return expr_;
        if(expr_==_ex0)
            return expr_;

        try
        {
            ex temexpr_ = Collect_common_factors.expr_visitor(normal(expr_)), xprev;
            ex numer_denomClt;
            exmap temBaseClt,temexprToSymMap;   // It stores the values of variables in subclasses of map_function.
                // All the subclasses of same base class map_function, when works at the same time,
                // the variables of subclasses are influenced by each other. To remove this problem, variables in subclasses
                // are stored by other variables before use of second subclasses. Here the subclasses fracPowBasSubsE,
                // and fracPowBasSubsFactor (used in Factor) has been used at the same time.


            if(expr_.info(info_flags::relation)) // including relation operator (==)
                temexpr_ = expr_.rhs();

            temexpr_ = temexpr_.subs(externSymbols.factSymb_==_ex1);

//            std::cout<<temexpr_<<std::endl;
            if(rules==simplify_options::HyperSimp||rules==simplify_options::TrigSimp
                ||rules==simplify_options::JacobiSimp||rules==simplify_options::FuncSimp)
            {
                temexpr_=Simplify(temexpr_,rules);
//                std::cout<<"jj "<<temexpr_<<std::endl;
                funcSubsE.set();
                temexpr_ = funcSubsE.expr_visitor(temexpr_);
                rules = simplify_options::AlgSimp;
            }
//            std::cout<<temexpr_<<std::endl;

            temexpr_=Simplify(temexpr_,rules);

            //std::cout<<temexpr_<<std::endl;
            if(is_a<numeric>(temexpr_)) // This return numeric expressions without more simplify.
            {
                if(expr_.info(info_flags::relation))
                    return expr_.lhs()==(temexpr_);
                return  temexpr_;
            }

            powBaseSubsLessThanDeg baseSubs(0);     // At first all expressions having degree less than expandLevel is expanded
            temexpr_ = baseSubs.expr_visitor(temexpr_);          // and expressions having degree greater then expandLevel is replaced by
            temexpr_=Simplify(temexpr_,rules);      // generated symbols.
            temexprToSymMap = baseSubs.exprToSymMap;

            //std::cout<<temexpr_<<std::endl;

            //cout<<temexpr_<<endl;
            numer_denomClt = Numer_Denom(temexpr_);
            temexpr_ = Simplify((is_a<numeric>(numer_denomClt.op(0))?numer_denomClt.op(0):collect_common_factors((Factor(Simplify(expand(numer_denomClt.op(0)/*,expand_options::expand_function_args*/),rules)))))/
                                    (is_a<numeric>(numer_denomClt.op(1))?numer_denomClt.op(1):collect_common_factors((Factor(Simplify(expand(numer_denomClt.op(1)/*,expand_options::expand_function_args*/),rules))))),rules);


            do // This collect common numerical factors inside base of fractional power.
            {
                xprev =temexpr_;
                temexpr_ = Collect_common_factors.expr_visitor(temexpr_);
                temexpr_ = temexpr_.subs(externSymbols.factSymb_==_ex1);
                temexpr_ = Simplify(temexpr_,rules);

            } while(xprev != temexpr_);
            temexpr_ = temexpr_.subs(externSymbols.factSymb_==_ex1);
            //cout<<temexpr_<<endl;


            fracPowBasSubsE.set();
            temexpr_=fracPowBasSubsE.expr_visitor(temexpr_);
            if(!fracPowBasSubsE.baseClt.empty())
            {
                ex temtemexpr_;
                temBaseClt = fracPowBasSubsE.baseClt;
                for(auto it = temBaseClt.begin(); it != temBaseClt.end(); it++)
                {
                    if(temexpr_.is_polynomial((*it).second))
                    {
                        temtemexpr_ = _ex0;
                        temexpr_ = expand(temexpr_);
                        for(int i = 0; i <=degree(temexpr_,(*it).second); i++)
                        {
                            numer_denomClt = (temexpr_.coeff((*it).second,i)).numer_denom();
                            temtemexpr_ = temtemexpr_+ pow((*it).second,i)*Simplify((is_a<numeric>(numer_denomClt.op(0))?numer_denomClt.op(0):collect_common_factors((Factor(Simplify((numer_denomClt.op(0)),rules)))))/
                                                                                            (is_a<numeric>(numer_denomClt.op(1))?numer_denomClt.op(1):collect_common_factors((Factor(Simplify((numer_denomClt.op(1)),rules))))),rules);
                        }
                        temexpr_ = temtemexpr_;
                    }
                    else
                    {
                        numer_denomClt = temexpr_.numer_denom();
                        temexpr_ = Simplify((is_a<numeric>(numer_denomClt.op(0))?numer_denomClt.op(0):collect_common_factors((Factor(Simplify(expand(numer_denomClt.op(0)),rules)))))/
                                                (is_a<numeric>(numer_denomClt.op(1))?numer_denomClt.op(1):collect_common_factors((Factor(Simplify(expand(numer_denomClt.op(1)),rules))))),rules);
                    }
                }

                temexpr_ = Simplify(genSymbSubs(temexpr_,temBaseClt),rules);
                fracPowBasSubsE.set();
                //cout<<temexpr_<<endl;
            }


            //cout<<temexpr_<<endl;
            numer_denomClt = Numer_Denom(temexpr_);
            temexpr_ = Simplify((is_a<numeric>(numer_denomClt.op(0))?numer_denomClt.op(0):collect_common_factors((Factor(Simplify(expand(numer_denomClt.op(0)),rules)))))/
                                    (is_a<numeric>(numer_denomClt.op(1))?numer_denomClt.op(1):collect_common_factors((Factor(Simplify(expand(numer_denomClt.op(1)),rules))))),rules);

            //cout<<temexpr_<<endl;

            temexpr_ = Simplify(genSymbSubs(temexpr_,temexprToSymMap),rules);

            if(!funcSubsE.baseClt.empty())
            {
                temexpr_ = Simplify(genSymbSubs(temexpr_,funcSubsE.baseClt),rules);
                funcSubsE.set();

                temexpr_=Simplify(temexpr_,simplify_options::FuncSimp);
            }


            //std::cout<<temexpr_<<std::endl;
            temexpr_=Simplify(someMoreSimpRulesE.expr_visitor(temexpr_));

            if(expr_.info(info_flags::relation))
                return expr_.lhs()==(temexpr_);

            return (temexpr_);
        }

        catch(ginacsym::pole_error){return expr_.subs(externSymbols.factSymb_==_ex1);}
        catch (cln::runtime_exception){return expr_.subs(externSymbols.factSymb_==_ex1);}

        catch(std::invalid_argument){return expr_.subs(externSymbols.factSymb_==_ex1);}
        catch(std::out_of_range){return expr_.subs(externSymbols.factSymb_==_ex1);}

        return (expr_);
    }

    ex fullsimplify(const ex& expr_, unsigned int rules)
    {
        ex prev, curr = expr_;

        do
        {
            prev = curr;
            curr = simplify(curr, rules);
        }while(prev!=curr);

        return  curr;
    }
}
/////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////


