
/** @file inert.cpp
 *
 *  Implementation of class Diff, Integrate. */

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

#include "inifcns.h"
#include "ex.h"
#include "constant.h"
#include "mul.h"
#include "power.h"
#include "operators.h"
#include "relational.h"
#include "pseries.h"
#include "symbol.h"
#include "utils.h"
#include "infinity.h"
#include "add.h"
#include "mul.h"

#include "inert.h"
#include "fail.h"
#include "ginacwrapper.h"
#include "simplify.h"
#include "functions.h"
#include "integrate.h"
#include "limit.h"


namespace ginacsym {

GINAC_IMPLEMENT_REGISTERED_CLASS_OPT(Diff,basic,
                                     print_func<print_dflt>(&Diff::do_print).
                                     print_func<print_python>(&Diff::do_print_python).
                                     print_func<print_latex>(&Diff::do_print_latex))

////////////// Diff ///////////////////////////////
/// \brief Diff::Diff
///
Diff::Diff() {}
////////
/// \brief Diff::Diff
/// \param d
/// \param i
/// \param o
///
Diff::Diff(const ex& d, const ex& i, const ex& o):de(d),ind(i),order(o){}

int Diff::compare_same_type(const basic& other) const
{
    GINAC_ASSERT(is_exactly_a<Diff>(other));
    const Diff &o = static_cast<const Diff &>(other);

    int cmpval = order.compare(o.order);
    if (cmpval)
        return cmpval;
    cmpval = ind.compare(o.ind);
    if (cmpval)
        return cmpval;
    return de.compare(o.de);

}
void Diff::do_print(const  print_context& c,unsigned level) const{
    c.s<<"Diff(";
    de.print(c);
    c.s<<",";
    ind.print(c);
    c.s<<",";
    order.print(c);
    c.s<<")";
}

void Diff::do_print_python(const  print_python& c,unsigned level) const{
    c.s<<"Diff(";
    de.print(c);
    c.s<<",";
    ind.print(c);
    c.s<<",";
    order.print(c);
    c.s<<")";
}

void Diff::do_print_latex(const  print_latex& c,unsigned level) const{
    if(!is_partial(de)){
        if(!order.is_equal(1)){
            c.s << "\\frac{d^";c.s<<order;c.s << "}{d";ind.print(c);
            c.s<<"^";c.s<<order;c.s<<"}";c.s<<"\\left(";de.print(c);c.s<<"\\right)";
        }
        else{
            c.s << "\\frac{d"; c.s << "}{d";ind.print(c);
            c.s<<"}";c.s<<"\\left(";de.print(c);c.s<<"\\right)";
        }
    }
    else{
        if(!order.is_equal(1)){
            c.s << "\\frac{\\partial^";c.s<<order;c.s << "}{\\partial ";ind.print(c);
            c.s<<"^";c.s<<order;c.s<<"}";c.s<<"\\left(";de.print(c);c.s<<"\\right)";
        }
        else {
            c.s << "\\frac{\\partial";c.s << "}{\\partial ";ind.print(c);
            c.s<<"}";c.s<<"\\left(";de.print(c);c.s<<"\\right)";
        }
    }
}


///
/// \brief Diff::eval
///
ex Diff::eval() const{

    if(order.is_equal(0))
        return de;

//    if(is_a<Diff>(de)){//handling Diff function
//        if((de).op(1).is_equal(ind))
//            return dynallocate<Diff>(Diff(de.op(0),de.op(1),add(de.op(2),order)));
//        else if((de).op(0).has(ind))
//            return (*this).hold();
//        else return 0;
//    }
//    else if(!de.has(ind))
//        return 0;
    return (*this).hold();
}

ex Diff::eval_ncmul(const exvector & v) const
{
    return de.eval_ncmul(v);
}

ex Diff::derivative(const symbol& s) const
{
    if(ex(s).is_equal(ind))
        return dynallocate<Diff>(Diff(de,ind,order+1));
    else if((de).has(ind))
        return dynallocate<Diff>(Diff((*this),s,order));
    else return 0;
}

ex& Diff::let_op(size_t i)
{
    switch (i) {
    case 0:
        return de;
    case 1:
        return ind;
    case 2:
        return order;
    default:
        throw (std::out_of_range("Diff::op() out of range"));
    }
}

ex Diff::subs(const exmap& m, unsigned options) const
{
    return  dynallocate<Diff>(de.subs(m,options),ind,order);
}

ex Diff::expand(unsigned options) const
{
    if (options==0 && (flags & status_flags::expanded))
        return *this;

    const ex newde = de.expand(options);

    if (is_a<add>(newde)) {
        exvector v;
        v.reserve(newde.nops());
        for (size_t i=0; i<newde.nops(); ++i)
            v.push_back(Diff(newde.op(i),ind,order).expand(options));
        return ex(add(v)).expand(options);
    }
    else {
        if (options==0)
            this->setflag(status_flags::expanded);
        return *this;
    }
}

ex Diff::op(const size_t i) const
{
    switch (i) {
    case 0:
        return de;
    case 1:
        return ind;
    case 2:
        return order;
    default:
        throw (std::out_of_range("Diff::op() out of range"));
    }
}

unsigned Diff::return_type() const
{
    return de.return_type();
}

return_type_t Diff::return_type_tinfo() const
{
    return de.return_type_tinfo();
}

ex Diff::evaluate() const
{
    if(is_a<functions>(de))
        return Diff(de,ind,order);
    else
        return de.diff(ex_to<symbol>(ind),ex_to<numeric>(order).to_int());
}

ex Diff::changeVariable(const ex& oldNewOrNewOld, const ex& newvarName) const
{
    if(oldNewOrNewOld.lhs()!=newvarName){//(oldVar==f(newVar),newVar)

            //substituting new variable and making change of variable
        ex denew=de;//simplify(de.subs(oldNewOrNewOld));
        for (int i = 1; i <= ex_to<numeric>(order); ++i) {
            denew=dynallocate<Diff>(Diff(denew,newvarName))/Simplify(oldNewOrNewOld.rhs().diff(ex_to<symbol>(newvarName)));
        }

        return (denew);
    }
    else{//(newVar==f(oldVar),newVar)
        try{
            const ex  oldNew=lsolve(oldNewOrNewOld,ind),
                newvarName=oldNewOrNewOld.lhs();
            //substituting new variable and making change of variable
            ex denew=de;//simplify(de.subs(ind==oldNew));

            for (int i = 1; i <= ex_to<numeric>(order); ++i) {
                denew=dynallocate<Diff>(Diff(denew,newvarName))/Simplify(oldNew.diff(ex_to<symbol>(newvarName)));
            }

            return (denew);
        }
        catch(std::logic_error){
            ex  newvarName=oldNewOrNewOld.lhs();
            //substituting new variable and making change of variable
            ex denew=de;//simplify(de.subs(oldNewOrNewOld.rhs()==oldNewOrNewOld.lhs(),subs_options::algebraic));

            for (int i = 1; i <= ex_to<numeric>(order); ++i) {
                denew=dynallocate<mul>(dynallocate<Diff>(Diff(denew,newvarName)),Simplify(oldNewOrNewOld.rhs().diff(ex_to<symbol>(ind))));
            }

            return (denew);
        }
        return *this;
    }

}

///partial Diff check//////
bool is_partial(const ex& expr)
{
    exset symbolClt;
    for(auto itr=expr.preorder_begin();itr!=expr.preorder_end();itr++){
        if(is_a<symbol>(*itr))
            symbolClt.insert(*itr);
        if(symbolClt.size()>1)
            return true;
    }
    return false;
}

                                    /////Integrate//////

GINAC_IMPLEMENT_REGISTERED_CLASS_OPT(Integrate,basic,
                                     print_func<print_dflt>(&Integrate::do_print).
                                     print_func<print_python>(&Integrate::do_print_python).
                                     print_func<print_latex>(&Integrate::do_print_latex))
Integrate::Integrate(){}

int Integrate::compare_same_type(const basic& other) const
{
    GINAC_ASSERT(is_exactly_a<Integrate>(other));
    const Integrate &o = static_cast<const Integrate &>(other);

    if(is_definite){
        int cmpval = var.compare(o.var);
        if (cmpval)
            return cmpval;
        cmpval = l.compare(o.l);
        if (cmpval)
            return cmpval;
        cmpval = u.compare(o.u);
        if (cmpval)
            return cmpval;
        return integrand.compare(o.integrand);
    }
    else{
        const int cmpval = var.compare(o.var);
        if (cmpval)
            return cmpval;
        return integrand.compare(o.integrand);
    }
}


void Integrate::do_print(const print_context & c, unsigned level) const
{
    if(is_definite){
        c.s << "Integrate(";
        integrand.print(c);
        c.s << ",";
        var.print(c);
        c.s << ",";
        l.print(c);
        c.s << ",";
        u.print(c);
        c.s << ")";
    }
    else{
        c.s << "Integrate(";
        integrand.print(c);
        c.s << ",";
        var.print(c);
        c.s << ")";
    }
}

void Integrate::do_print_python(const print_python & c, unsigned level) const
{
    if(is_definite){
        c.s << "Integrate(";
        integrand.print(c);
        c.s << ",";
        var.print(c);
        c.s << ",";
        l.print(c);
        c.s << ",";
        u.print(c);
        c.s << ")";
    }
    else{
        c.s << "Integrate(";
        integrand.print(c);
        c.s << ",";
        var.print(c);
        c.s << ")";
    }
}

void Integrate::do_print_latex(const print_latex & c, unsigned level) const
{
    if(is_definite){
        c.s << "\\displaystyle\\int_{";
        l.print(c);
        c.s<<"}";
        c.s<<"^{";
        u.print(c);
        c.s<<"}";
        if(is_a<add>(integrand)){
            c.s<<"(";
            integrand.print(c);
            c.s<<")";
        }
        else{
            c.s<<" ";
            integrand.print(c);
            c.s<<" ";
        }
        c.s << "d";
        var.print(c);
    }
    else{
        c.s << "\\displaystyle\\int";
        if(is_a<add>(integrand)){
            c.s<<"(";
            integrand.print(c);
            c.s<<")";
        }
        else{
            c.s<<" ";
            integrand.print(c);
            c.s<<" ";
        }
        c.s << "d";
        var.print(c);
    }
}

ex Integrate::derivative(const symbol& s) const
{
    if(is_definite){
        return u.diff(s)*integrand.subs(var==u)-l.diff(s)*integrand.subs(var==l)
               +Integrate(integrand.diff(s),var, l, u);
    }
    else{
        if(s.is_equal(ex_to<basic>(var)))
            return integrand;
        else return dynallocate<Integrate>(Integrate(integrand.diff(s),var));
    }
}

ex Integrate::eval() const
{
    if(integrand.is_equal(_ex0))
        return _ex0;
//    if(!is_definite && !integrand.has(var))
//        return integrand*var;
    if(is_definite && l.is_equal(u))
        return _ex0;
    return (*this).hold();
}

ex Integrate::eval_ncmul(const exvector & v) const
{
    return integrand.eval_ncmul(v);
}

size_t Integrate::nops() const
{
    if(is_definite)
        return 4;
    else return 2;
}

ex Integrate::op(size_t i) const
{
    if(is_definite){
        GINAC_ASSERT(i<4);

        switch (i) {
        case 0:
            return integrand;
        case 1:
            return var;
        case 2:
            return l;
        case 3:
            return u;
        default:
            throw (std::out_of_range("Integrate::op() out of range"));
        }
    }
    else{
        GINAC_ASSERT(i<2);

        switch (i) {
        case 0:
            return integrand;
        case 1:
            return var;
        default:
            throw (std::out_of_range("Integrate::op() out of range"));
        }
    }
}

ex & Integrate::let_op(size_t i)
{
    ensure_if_modifiable();
    if(is_definite){
        GINAC_ASSERT(i<4);

        switch (i) {
        case 0:
            return integrand;
        case 1:
            return var;
        case 2:
            return l;
        case 3:
            return u;
        default:
            throw (std::out_of_range("Integrate::op() out of range"));
        }
    }
    else{
        GINAC_ASSERT(i<2);

        switch (i) {
        case 0:
            return integrand;
        case 1:
            return var;
        default:
            throw (std::out_of_range("Integrate::op() out of range"));
        }
    }
}

ex Integrate::expand(unsigned options) const
{
    if (options==0 && (flags & status_flags::expanded))
        return *this;

    if(is_definite){
        ex newl = l.expand(options);
        ex newu = u.expand(options);
        ex newintegrand = integrand.expand(options);

        if (is_a<add>(newintegrand)) {
            exvector v;
            v.reserve(newintegrand.nops());
            for (size_t i=0; i<newintegrand.nops(); ++i)
                v.push_back(Integrate(newintegrand.op(i),var, newl, newu,partial_num).expand(options));
            return ex(add(v)).expand(options);
        }

        if (is_a<mul>(newintegrand)) {
            ex prefactor = 1;
            ex rest = 1;
            for (size_t i=0; i<newintegrand.nops(); ++i)
                if (newintegrand.op(i).has(var))
                    rest *= newintegrand.op(i);
                else
                    prefactor *= newintegrand.op(i);
            if (prefactor != 1)
                return (prefactor*Integrate(rest,var, newl, newu,partial_num)).expand(options);
        }

        if (are_ex_trivially_equal(l, newl) && are_ex_trivially_equal(u, newu) &&
            are_ex_trivially_equal(integrand, newintegrand)) {
            if (options==0)
                this->setflag(status_flags::expanded);
            return *this;
        }

        const Integrate & newint = dynallocate<Integrate>(newintegrand,var, newl, newu,partial_num);
        if (options == 0)
            newint.setflag(status_flags::expanded);
        return newint;
    }
    else{
        ex newintegrand = integrand.expand(options);

        if (is_a<add>(newintegrand)) {
            exvector v;
            v.reserve(newintegrand.nops());
            for (size_t i=0; i<newintegrand.nops(); ++i)
                v.push_back(Integrate(newintegrand.op(i),var,partial_num).expand(options));
            return ex(add(v)).expand(options);
        }

        if (is_a<mul>(newintegrand)) {
            ex prefactor = 1;
            ex rest = 1;
            for (size_t i=0; i<newintegrand.nops(); ++i)
                if (newintegrand.op(i).has(var))
                    rest *= newintegrand.op(i);
                else
                    prefactor *= newintegrand.op(i);
            if (prefactor != 1)
                return (prefactor*Integrate(rest,var,partial_num)).expand(options);
        }

        if (are_ex_trivially_equal(integrand, newintegrand)) {
            if (options==0)
                this->setflag(status_flags::expanded);
            return *this;
        }

        const Integrate & newint = dynallocate<Integrate>(newintegrand,var,partial_num);
        if (options == 0)
            newint.setflag(status_flags::expanded);
        return newint;

    }
}

ex Integrate::subs(const exmap& m, unsigned options) const
{
    ex newintegrand=integrand.subs(m,options);
    if (is_definite) {
        ex  newl=l.subs(m,options),
            newu=u.subs(m,options);
        return  dynallocate<Integrate>(newintegrand,var, newl, newu,partial_num);
    }
    else return  dynallocate<Integrate>(newintegrand,var,partial_num);
}

unsigned Integrate::return_type() const
{
    return integrand.return_type();
}

return_type_t Integrate::return_type_tinfo() const
{
    return integrand.return_type_tinfo();
}

ex Integrate::conjugate() const
{
    if(is_definite){
        ex conjintegrand = integrand.conjugate().subs(var.conjugate()==var);
        ex conjl = l.conjugate();
        ex conju = u.conjugate();


        if (are_ex_trivially_equal(l, conjl) && are_ex_trivially_equal(u, conju) &&
            are_ex_trivially_equal(integrand, conjintegrand))
            return *this;

        return dynallocate<Integrate>(conjintegrand,var, conjl, conju,partial_num);
    }
    else{
        ex conjintegrand = integrand.conjugate().subs(var.conjugate()==var);

        if (are_ex_trivially_equal(integrand, conjintegrand))
            return *this;

        return dynallocate<Integrate>(conjintegrand,var,partial_num);
    }
}

Integrate Integrate::changeVariable(const ex& oldNewOrNewOld, const ex& newvarName) const
{
    if(oldNewOrNewOld.lhs()!=newvarName){//(oldVar==f(newVar),newVar)
        if(is_definite){//substituting new variable and making change of variable in definite integration
            //solving equation oldNewOrNewOld.lhs()-oldNewOrNewOld.rhs()=0, for newvarName
            ex equa = oldNewOrNewOld.lhs()-oldNewOrNewOld.rhs(),
                temequa = equa,funcName;
            symbol funcSubs("funcSubs");
            unsigned newvarNameNum=0;
            for(const_preorder_iterator itr = equa.preorder_begin(); itr != equa.preorder_end(); itr++){
                if (is_a<function>(*itr) && (*itr).op(0).has(newvarName)) {
                    if(newvarNameNum>0)
                        return (*this);
                    temequa=temequa.subs(*itr==funcSubs);
                    funcName=*itr;
                    ++newvarNameNum;
                }
            }
            if(temequa.has(newvarName) && temequa.has(funcSubs))
                return *this;
            if(!temequa.is_polynomial(newvarName))
                return *this;
            else if (temequa.degree(newvarName)>1)
                return *this;
            ex lnew;
            ex unew;

            if ((temequa).has(newvarName)) {
                lnew=lsolve({temequa==0},{newvarName});
                unew=lsolve({temequa==0},{newvarName});
            }
            else {
                lnew=lsolve({temequa==0},{funcSubs});
                unew=lsolve({temequa==0},{funcSubs});
                const std::vector<std::string> trigname={"sin","cos","tan","cot","csc","sec",
                                                        "sinh","cosh","tanh","coth","csch","sech"};
                if(std::find(trigname.begin(),trigname.end(),ex_to<function>(funcName).get_name())!=trigname.end()){
                    const std::string funcSolve="arc"+ex_to<function>(funcName).get_name()+to_string(lnew);
                    lnew=generator.exGeneratorFromString("arc"+ex_to<function>(funcName).get_name()+"("+to_string(lnew)+")").subs(var==l);
                    unew=generator.exGeneratorFromString("arc"+ex_to<function>(funcName).get_name()+"("+to_string(unew)+")").subs(var==u);
                }
                else return *this;

            }

            ex integrandnew=integrand;//simplify(integrand.subs(oldNewOrNewOld));
            integrandnew=simplify(integrandnew*(oldNewOrNewOld.rhs().diff(ex_to<symbol>(newvarName))));
            return dynallocate<Integrate>(Integrate(integrandnew,newvarName,lnew, unew,partial_num));
        }
        else{//substituting new variable and making change of variable in indefinite integration
            ex integrandnew=integrand;//simplify(integrand.subs(oldNewOrNewOld));
            integrandnew=simplify(integrandnew*(oldNewOrNewOld.rhs().diff(ex_to<symbol>(newvarName))));
            return dynallocate<Integrate>(Integrate(integrandnew,newvarName,partial_num));
        }
    }
    else{//(newVar==f(oldVar),newVar)
        try{
            const ex  oldNew=lsolve(oldNewOrNewOld,var),
                newvarName=oldNewOrNewOld.lhs();

            if(is_definite){//substituting new variable and making change of variable in definite integration
                const ex lnew=lsolve({oldNew==l},{newvarName});
                const ex unew=lsolve({oldNew==u},{newvarName});

                ex integrandnew=integrand;//simplify(integrand.subs(var==oldNew));
                integrandnew=simplify(integrandnew*(oldNew.diff(ex_to<symbol>(newvarName))));
                return dynallocate<Integrate>(Integrate(integrandnew,newvarName,lnew, unew,partial_num));
            }
            else{//substituting new variable and making change of variable in indefinite integration
                ex integrandnew=integrand;//simplify(integrand.subs(var==oldNew));
                integrandnew=simplify(integrandnew*(oldNew.diff(ex_to<symbol>(newvarName))));
                return dynallocate<Integrate>(Integrate(integrandnew,newvarName,partial_num));
            }
        }
        catch(std::logic_error){
            ex  newvarName=oldNewOrNewOld.lhs();

            if(is_definite){//substituting new variable and making change of variable in definite integration
                const ex lnew=oldNewOrNewOld.rhs().subs(var==l);
                const ex unew=oldNewOrNewOld.rhs().subs(var==u);

                ex integrandnew=integrand;//simplify(integrand.subs(oldNewOrNewOld.rhs()==oldNewOrNewOld.lhs(),subs_options::algebraic));
                integrandnew=simplify(integrandnew*(1/oldNewOrNewOld.rhs().diff(ex_to<symbol>(var))));
                return dynallocate<Integrate>(Integrate(integrandnew,newvarName,lnew, unew,partial_num));
            }
            else{//substituting new variable and making change of variable in indefinite integration
                ex integrandnew=integrand;//simplify(integrand.subs(oldNewOrNewOld.rhs()==oldNewOrNewOld.lhs(),subs_options::algebraic));
                integrandnew=simplify(integrandnew*(1/oldNewOrNewOld.rhs().diff(ex_to<symbol>(var))));
                return dynallocate<Integrate>(Integrate(integrandnew,newvarName,partial_num));
            }
        }
        return *this;
    }

}

ex Integrate::apply_partial_integration() const
{
    //constant term integration//
    if (!integrand.has(var)) {
        return var*integrand;
    }

    //separating constant and variable dependent expression//
    ex constex=_ex1,varex=_ex1;
    if (is_a<mul>(integrand)) {
        //cout<<integrand<<endl;
        for(const_iterator itr=integrand.begin();itr!=integrand.end();++itr){
            if (!(*itr).has(var)) {
                constex=constex*(*itr);
            }
            else {
                varex=varex*(*itr);
            }
        }
    }
    else {
        varex=integrand;
    }

    exvector LIATE=Liate(varex,var);

    //        for(auto itr:LIATE) cout<<"jj "<<itr<<endl;


    //prtial integration//
    if (LIATE.size()==0){
        if(!is_definite)
            return constex*Integrate(varex,var,1);
        else
            return constex*Integrate(varex,var,l,u,1);
    }
    else if (LIATE.size()==1){
        //            cout<<"LIATE[0]1 "<<func_inte(LIATE[0])<<endl;
        if(!is_definite)
            return constex*func_inte(LIATE[0],var,1);
        else{
            ex tem=func_inte(LIATE[0],var,1);
            if(is_a<Integrate>(tem))
                return constex*tem;
            else return constex*(tem.subs(var==u)-tem.subs(var==l));
        }

    }

    else if (LIATE.size()==2) {
        if(!is_definite)
            return constex*(LIATE[0]*func_inte(LIATE[1],var,1).expand()).expand()
               -constex*dynallocate<Integrate>(LIATE[0].diff(ex_to<symbol>(var))*func_inte(LIATE[1],var,1).expand(),var,1).expand();
        else{
            ex tem=func_inte(LIATE[1],var,1);
            if(is_a<Integrate>(tem))
            return constex*(LIATE[0]*dynallocate<Integrate>(LIATE[1],var,l,u,1).expand()).expand()
                   -constex*dynallocate<Integrate>(LIATE[0].diff(ex_to<symbol>(var))*dynallocate<Integrate>(LIATE[1],var,l,u,1).expand(),var,l,u,1).expand();
            else {
                constex*(LIATE[0]*(tem.subs(var==u)-tem.subs(var==l))).expand()
                    -constex*dynallocate<Integrate>(LIATE[0].diff(ex_to<symbol>(var))*(tem.subs(var==u)-tem.subs(var==l)),var,l,u,1).expand();

            }
        }
    }

    else /*if(LIATE.size()==3)*/ {
        ex partiaSecondTerm=dynallocate<Integrate>(ex(mul(exvector(LIATE.begin()+1,LIATE.end()))),var,1).apply_partial_integration().expand();
        if(is_definite){
            if(!is_a<Integrate>(partiaSecondTerm))
                partiaSecondTerm=(partiaSecondTerm.subs(var==u)-partiaSecondTerm.subs(var==l)).expand();
        }
        //            cout<<"partiaSecondTerm "<<partiaSecondTerm<<endl;
        if(!is_definite)
            return constex*LIATE[0]*(partiaSecondTerm)
                       -constex*dynallocate<Integrate>(LIATE[0].diff(ex_to<symbol>(var))*(partiaSecondTerm),var,1);
        else
            return constex*LIATE[0]*(partiaSecondTerm)
                   -constex*dynallocate<Integrate>(LIATE[0].diff(ex_to<symbol>(var))*(partiaSecondTerm),var,l,u,1);
    }
    if(!is_definite)
        return Integrate(integrand,var,1);
    else
        return Integrate(integrand,var,l,u,1);
}


ex Integrate::evaluate() const
{
    if (is_definite) {
        return ginacsym::integrate(integrand,var,l,u,partial_num);
    }
    else
        return ginacsym::integrate(integrand,var,partial_num);
}

                        ////Limit///////
GINAC_IMPLEMENT_REGISTERED_CLASS_OPT(Limit,basic,
                                     print_func<print_dflt>(&Limit::do_print).
                                     print_func<print_python>(&Limit::do_print_python).
                                     print_func<print_latex>(&Limit::do_print_latex))


Limit::Limit() {}

Limit::Limit(const ex& e,const ex& z,const ex& z0, const std::string& _dir):expr(e),var(z),value(z0),dir(_dir){}

int Limit::compare_same_type(const basic& other) const
{
    GINAC_ASSERT(is_exactly_a<Limit>(other));
    const Limit &o = static_cast<const Limit &>(other);

    if(dir!=o.dir)
        return 1;
    int cmpval = value.compare(o.value);
    if (cmpval)
        return cmpval;
    cmpval = var.compare(o.var);
    if (cmpval)
        return cmpval;
    return expr.compare(o.expr);

}

void Limit::do_print(const  print_context& c,unsigned level) const{
    c.s<<"Limit(";
    expr.print(c);
    c.s<<",";
    var.print(c);
    c.s<<",";
    value.print(c);
    if(dir=="+")
        c.s<<",+";
    else if(dir=="-")
        c.s<<",-";
    c.s<<")";
}

void Limit::do_print_python(const  print_python& c,unsigned level) const{
    c.s<<"Limit(";
    expr.print(c);
    c.s<<",";
    var.print(c);
    c.s<<",";
    value.print(c);
    if(dir=="+")
        c.s<<",+";
    else if(dir=="-")
        c.s<<",-";
    c.s<<")";
}

void Limit::do_print_latex(const  print_latex& c,unsigned level) const
{
    c.s << "\\displaystyle\\lim_{";
    var.print(c);
    c.s << "\\to ";
    value.print(c);
    if(dir=="+")
        c.s<<"+";
    else if(dir=="-")
        c.s<<"-";
    c.s << "}";
    if(is_a<add>(expr)){
        c.s<<"\\left(";expr.print(c);c.s<<"\\right)";
    }
    else
        expr.print(c);
}


ex Limit::eval_ncmul(const exvector & v) const
{
    return expr.eval_ncmul(v);
}


ex& Limit::let_op(size_t i)
{
    switch (i) {
    case 0:
        return expr;
    case 1:
        return var;
    case 2:
        return value;
    default:
        throw (std::out_of_range("Limit::op() out of range"));
    }
}


ex Limit::op(const size_t i) const
{
    switch (i) {
    case 0:
        return expr;
    case 1:
        return var;
    case 2:
        return value;
    default:
        throw (std::out_of_range("Limit::op() out of range"));
    }
}

ex Limit::subs(const exmap& m, unsigned options) const
{
    return  dynallocate<Limit>(expr.subs(m,options),var,value.subs(m,options),dir);
}

ex Limit::expand(unsigned options) const
{
    if (options==0 && (flags & status_flags::expanded))
        return *this;

    const ex newexpr = expr.expand(options);

    if (is_a<add>(newexpr)) {
        exvector v;
        v.reserve(newexpr.nops());
        for (size_t i=0; i<newexpr.nops(); ++i)
            v.push_back(Limit(newexpr.op(i),var,value,dir).expand(options));
        return ex(add(v)).expand(options);
    }
    else {
        if (options==0)
            this->setflag(status_flags::expanded);
        return *this;
    }
}



unsigned Limit::return_type() const
{
    return expr.return_type();
}

return_type_t Limit::return_type_tinfo() const
{
    return expr.return_type_tinfo();
}

ex Limit::evaluate() const
{
    return ginacsym::limit(expr,var,value,dir);
}


ex apply_partial_integration_on_exc::expr_visitor(const ex& e)
{
    if(is_a<Integrate>(e)){
        return ex_to<Integrate>(e).apply_partial_integration();
    }

    return e.map(*this);
}

ex evaluatec::expr_visitor(const ex& e)
{
    if(is_a<Diff>(e)){
        return ex_to<Diff>(e).evaluate().map(*this);
    }
    else if(is_a<Limit>(e)){
        return ex_to<Limit>(e).evaluate().map(*this);
    }
    else if(is_a<Integrate>(e)){
        return ex_to<Integrate>(e).evaluate().map(*this);
    }

    return e.map(*this);
}

apply_partial_integration_on_exc apply_partial_integration_on_exE;
evaluatec evaluateE;

ex apply_partial_integration_on_ex(const ex& e, const unsigned int &partial_num)
{
    ex f=e;
    for (unsigned var = 0; var < partial_num; ++var) {
        f=apply_partial_integration_on_exE.expr_visitor(f);
    }
    return f;
}

ex evaluate(const ex& e)
{
    return evaluateE.expr_visitor(e);
}


}
