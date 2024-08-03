#include "limit.h"
#include "ginacwrapper.h"
#include "inert.h"
#include "infinity.h"
#include "simplify.h"
#include "utility.h"
#include "utils.h"
#include "inifcns.h"
#include "add.h"
#include "flags.h"
#include "mul.h"
#include "add.h"

namespace ginacsym {

ex limit_by_series(const ex& e, const ex& z, const ex& z0, const std::string dir)
{
    try {
        ex _e=e;

        if(is_a<infinity>(z0)){
            _e=_e.subs(z==1/externSymbols.symb_);
            _e=_e.subs(externSymbols.symb_==z);
        }
        else if (!z.is_zero()) {
            _e=_e.subs(z==externSymbols.symb_+z0);
            _e=_e.subs(externSymbols.symb_==z);
        }

        size_t i=1;
        ex _eseries=_e.series(z,i);

        while(_eseries.nops()==1) {
            i++;
            _eseries=_e.series(z,i);
        }

        _eseries= series_to_poly(_eseries);
        if(_eseries.has(z) and _eseries.is_equal(_e))
            return  Limit(e,z,z0,dir);
        else if(_eseries.has(z))
            return _ex0;
        else
            return _eseries;
    } catch (...) {
        return Limit(e,z,z0,dir);
    }
}

//select numerator and denominator for applying Lhospital rule
lst numer_denom_selection(const ex& expr, const ex& z,const ex& z0, bool& is_exponential_indeterminate_form)
{
    exmap matched;
    matched.clear();
    bool is_matched=false;
    ex f,g,exponential_indeterminate_const_multerm=_ex1;

    try {
        expr.subs(z==z0);
    } catch (ginacsym::indeterminate_error) {
        //(0*oo)->wild(0)*log(wild(1)) //natural logarithm
        if (expr.match(wild(0)*log(wild(1)),matched)
            && matched[wild(0)].has(z)) {
            f=log(matched[wild(1)]);
            g=expand(1/matched[wild(0)]);
            is_matched=true;
        }
        matched.clear();
        //(0*oo))->wild(0)*logb(wild(1),wild(2)) //general logarithm
        if (expr.match(wild(0)*logb(wild(1),wild(2)),matched)
            && matched[wild(1)].has(z)
            && matched[wild(2)].has(z)) {
            f=logb(matched[wild(1)],matched[wild(2)]);
            g=expand(1/matched[wild(0)]);
            is_matched=true;
        }

        matched.clear();
        //(1^oo), (0^0), (oo^0)->wild(0)*(wild(1)^wild(2)) //Exponential Indeterminate Forms
        if (expr.match(wild(0)*power(wild(1),wild(2)),matched)//
            && !matched[wild(0)].has(z)
            && matched[wild(1)].has(z)
            && matched[wild(2)].has(z)) {
            is_exponential_indeterminate_form=true;
            exponential_indeterminate_const_multerm=matched[wild(0)];
            f=log(matched[wild(1)]);
            g=expand(1/matched[wild(2)]);
            is_matched=true;
        }
        matched.clear();
        //(1^oo), (0^0), (oo^0)->(wild(1)^wild(2)) //Exponential Indeterminate Forms
        if (expr.match(power(wild(1),wild(2)),matched)
            && matched[wild(1)].has(z)
            && matched[wild(2)].has(z)) {
            is_exponential_indeterminate_form=true;
            f=log(matched[wild(1)]);
            g=expand(1/matched[wild(2)]);
            is_matched=true;
        }
    }

    ex numerdivide=_ex1,denomdivide=_ex1;
    if (!is_matched) {
        ex fnd =numer_denom(expr);
        f=Simplify(expand(fnd[0])),g=Simplify(expand(fnd[1]));
        bool is_indeterminate_error=false;

        try {//Isolating constant term with limit variable z in numerator f so that it does not give 0*Infinity error.
            f.subs(z==z0); //Ex: 3*y in (2*y+3*y*x)/(y*x-3)
            if (is_a<add>(f)) {
                for (int i = 0; i < nops(f); ++i) {
                    if (is_a<mul>(f.op(i))) {
                        if (f.op(i).has(z)) {
                            for (int j = 0; j < nops(f.op(i)); ++j) {
                                if (!f.op(i).op(j).has(z)) {
                                    numerdivide=numerdivide*f.op(i).op(j);
                                }
                            }
                        }
                    }
                }
            }
            else if (is_a<mul>(f)) {
                for (int j = 0; j < nops(f.op(j)); ++j) {
                    if (!f.op(j).has(z)) {
                        numerdivide=numerdivide*f.op(j);
                    }
                }
            }

        } catch (ginacsym::indeterminate_error) {//selecting the terms which give zero in indeterminate terms(0*oo),
            is_indeterminate_error=true;        //and also selecting constant terms with limit variable z,
            if (is_a<add>(f)) {                 //and assign to numerdivide.
                for (int i = 0; i < nops(f); ++i) {// Ex. y*x^2 in numer of (x*x+y*x*x*log(x))/2
                    try {
                        f.op(i).subs(z==z0);
                    } catch (ginacsym::indeterminate_error) {
                        if (is_a<mul>(f.op(i)) && f.op(i).has(z)) {
                            for (int j = 0; j < nops(f.op(i)); ++j) {
                                if (f.op(i).op(j).subs(z==z0).is_zero()
                                    || !f.op(i).op(j).has(z)) {
                                    numerdivide=numerdivide*f.op(i).op(j);
                                }
                            }
                        }
                    }
                }
            }
            else if (is_a<mul>(f)) {
                for (int j = 0; j < nops(f.op(j)); ++j) {
                    if (f.op(j).subs(z==z0).is_zero()
                        || !f.op(j).has(z)) {
                        numerdivide=numerdivide*f.op(j);
                    }
                }
            }

        }



        try {//Isolating constant term with limit variable z in denominator g so that it does not give 0*Infinity error.
            g.subs(z==z0);//Ex: y in (2*y+3*y*x)/(y*x-3)
            if (is_a<add>(g)) {
                for (int i = 0; i < nops(g); ++i) {
                    if (is_a<mul>(g.op(i))) {
                        if (g.op(i).has(z)) {
                            for (int j = 0; j < nops(g.op(i)); ++j) {
                                if (!g.op(i).op(j).has(z)) {
                                    denomdivide=denomdivide*g.op(i).op(j);
                                }
                            }
                        }
                    }
                }
            }
            else if (is_a<mul>(g)) {
                for (int j = 0; j < nops(g.op(j)); ++j) {
                    if (!g.op(j).has(z)) {
                        denomdivide=denomdivide*g.op(j);
                    }
                }
            }

        } catch (ginacsym::indeterminate_error) {//selecting the terms which give zero in indeterminate terms(0*oo),
            is_indeterminate_error=true;        //and also selecting constant terms with limit variable z,
            if (is_a<add>(g)) {                 //and assign to denomdivide.
                for (int i = 0; i < nops(g); ++i) {// Ex. y*x^2 in denom of 2/(x*x+y*x*x*log(x))
                    try {
                        g.op(i).subs(z==z0);
                    } catch (ginacsym::indeterminate_error) {
                        if (is_a<mul>(g.op(i)) && g.op(i).has(z)) {
                            for (int j = 0; j < nops(g.op(i)); ++j) {
                                if (g.op(i).op(j).subs(z==z0).is_zero()
                                    || !g.op(i).op(j).has(z)) {
                                    denomdivide=denomdivide*g.op(i).op(j);
                                }
                            }
                        }
                    }
                }
            }
            else if (is_a<mul>(g)) {
                for (int j = 0; j < nops(g.op(j)); ++j) {
                    if (g.op(j).subs(z==z0).is_zero()
                        || !g.op(j).has(z)) {
                        denomdivide=denomdivide*g.op(j);
                    }
                }
            }

        }

        if (is_indeterminate_error) {
            if (!numerdivide.is_equal(_ex1) || !denomdivide.is_equal(_ex1)) {
                f=Simplify(expand(f/(numerdivide*denomdivide)));
                g=Simplify(expand(g/(numerdivide*denomdivide)));
            }
            numerdivide=_ex1;
            denomdivide=_ex1;
        }
        else {
            if (!numerdivide.is_equal(_ex1)) {
                f=Simplify(expand(f/(numerdivide)));
            }
            if (!denomdivide.is_equal(_ex1)) {
                g=Simplify(expand(g/(denomdivide)));
            }
        }
    }

//    std::cout<<numerdivide/denomdivide<<std::endl;
    return lst{f,g,numerdivide/denomdivide,exponential_indeterminate_const_multerm};
}

ex limit_by_lhospital(const ex& f,const ex& g, const ex& z, const ex& z0, const std::string dir)
{
//    std::cout<<f<<" "<<g<<std::endl;
    lst fg;
    bool is_exponential_indeterminate_form=false;
    try {

        ex lv;
        ex  _f=f,
            _g=g,
            _fs=(f).subs(z==z0),
            _gs=(g).subs(z==z0);

        if( (_fs.has(Infinity) and !is_a<infinity>(_fs)) || //detecting symbol with Infinity
            (_gs.has(Infinity) and !is_a<infinity>(_gs))) {
            throw(indeterminate_error("error"));
        }
        fg.append(_fs);
        fg.append(_gs);

//        std::cout<<_fs<<" "<<_gs<<std::endl;
        while ((_fs.is_zero() && _gs.is_zero())
               || (is_a<infinity>(_fs) && is_a<infinity>(_gs))) {
            _f=_f.diff(ex_to<symbol>(z));
            _g=_g.diff(ex_to<symbol>(z));
            lv=_f/_g;
            lv=Simplify((lv), simplify_options::TrigCombine);
            lv=Simplify((lv), simplify_options::HyperCombine);
            fg=numer_denom_selection(lv,z,z0,is_exponential_indeterminate_form);
            _f=fg[0];_g=fg[1];
//            std::cout<<_f<<" "<<_g<<std::endl;
            _fs=(Simplify(expand(fg[0]))).subs(z==z0);
            _gs=Simplify(expand(fg[1])).subs(z==z0);

            if( (_fs.has(Infinity) and !is_a<infinity>(_fs)) || //detecting symbol with Infinity
                (_gs.has(Infinity) and !is_a<infinity>(_gs))) {
                throw(indeterminate_error("error"));
            }
        }
        if (!is_exponential_indeterminate_form) {
            return _fs/_gs;
        }
        else{
            return fg[3]*exp(_fs/_gs);
        }


    } catch (...) {

        try {
            ex den=Simplify((fg[1]/fg[0]).expand()),dens=_ex0;
            if (!is_exponential_indeterminate_form) {
                return _ex1/(limit(den,z,z0));//calculating limit of each oparand in den
            }
            else{
                return fg[3]*exp(_ex1/limit(den,z,z0));
            }

        } catch (...) {
            return Limit(f/g,z,z0,dir);
        }
    }
}



ex limit(const ex& e, const ex& z, const ex& z0, const std::string& dir)
{
    if(!e.has(z))
        return e;
    ex expr=expand(e);
    //isolating constant
    if(is_a<mul>(expr)){
        ex constterm=_ex1,varterm=_ex1;
        for (int i = 0; i < expr.nops(); ++i) {
            if (expr.op(i).has(z)) {
                varterm *= expr.op(i);
            }
            else constterm *= expr.op(i);
        }
        if(!constterm.is_equal(_ex1)){
//            std::cout<<"kkk "<<constterm<<std::endl;
        return constterm*limit(varterm,z,z0,dir);
        }
    }
    if(is_a<add>(expr)){//applying addition formula for limit
        ex limitvalue;
        for (int i = 0; i < nops(expr); ++i) {
            limitvalue=limitvalue+limit(expr.op(i),z,z0,dir);
        }
        return limitvalue;
    }

    expr = Simplify(expr, simplify_options::TrigCombine);
    expr = Simplify((expr), simplify_options::HyperCombine);
    exmap ma;
    expr=expr.to_polynomial(ma);
    expr=normal(expr);
    expr=expr.subs(ma);

    ex f,g;
    bool is_exponential_indeterminate_form=false;
    ex exponential_indeterminate_const_multerm=_ex1;
    lst fg=numer_denom_selection(expr,z,z0,is_exponential_indeterminate_form);
    f=fg[0];g=fg[1];exponential_indeterminate_const_multerm=fg[3];

    ex _f,_g,r,l;
    int _fsign=1,_gsign=1;
    bool is_both_side_limit_equal=false;
    if (dir=="+" || dir=="+-") {//right limit
        try {
            _f=f.subs(z==z0);
            _g=g.subs(z==z0);

//            std::cout<<f<<std::endl;
//            std::cout<<g<<std::endl;
            if ((_f.is_zero() && _g.is_zero())
                || (is_a<infinity>(_f) && is_a<infinity>(_g))) {
                r=limit_by_lhospital(f,g,z,z0,dir);

                if(!fg[2].has(z))
                    r=r*fg[2];
                else r=r*limit(fg[2],z,z0,dir);
                l=r;//both side limit is same.
                is_both_side_limit_equal=true;
            }
            else {
                if( (_f.has(Infinity) and !is_a<infinity>(_f)) || //detecting symbol with Infinity
                    (_g.has(Infinity) and !is_a<infinity>(_g))) {
                    if(is_a<infinity>(z0)){
                        expr=expr.subs(z==externSymbols.symb_);
                        expr=expr.subs(externSymbols.symb_==1/z);
                        return limit(expr,z,_ex0,dir);
                    }
                    throw(indeterminate_error("error"));
                }

                if(!fg[2].has(z))
                    r=_f/_g*fg[2];
                else r=_f/_g*limit(fg[2],z,z0,dir);

                if (!is_a<infinity>(z0) and is_number(_f) and is_number(_g)) {
                    if(_f.info(info_flags::real))
                        _fsign=(f.subs(z==z0+pow(10.0,-((long)Digits))).evalf()).info(info_flags::positive)?1:-1;
                    if(_g.info(info_flags::real))
                        _gsign=(g.subs(z==z0+pow(10.0,-((long)Digits))).evalf()).info(info_flags::positive)?1:-1;
                }
                numeric sign = _fsign/_gsign;
//                std::cout<<"sign "<<sign<<std::endl;
//                std::cout<<"r "<<r<<std::endl;
                if ((r.info(info_flags::negative) and sign.is_positive())
                    || (r.info(info_flags::positive) and sign.is_negative())) {
                    r= r*sign;
                }
            }

        } catch (...) {
            try {
//                std::cout<<"e "<<std::endl;
                r= limit_by_series(expr,z,z0,dir);
                if(!fg[2].has(z))
                    r=r*fg[2];
                else r=r*limit(fg[2],z,z0,dir);

                l=r;
                is_both_side_limit_equal=true;
            } catch (...) {

                r= Limit(e,z,z0,dir);
            }
        }
    }


    if (dir=="-" || dir=="+-") {//left limit
        try {
            if (dir=="-") {
                _f=f.subs(z==z0);
                _g=g.subs(z==z0);
            }

            bool is_hospital_apply = false;
            if(dir=="-"){
                if ((_f.is_zero() && _g.is_zero())
                    || (is_a<infinity>(_f) && is_a<infinity>(_g))) {
                    l=limit_by_lhospital(f,g,z,z0,dir);
                    if(!fg[2].has(z))
                        l=l*fg[2];
                    else l=l*limit(fg[2],z,z0,dir);

                    is_hospital_apply=true;
                }
            }

            if ((dir=="+-" and !is_both_side_limit_equal)
                || (!is_hospital_apply)) {
                if(!fg[2].has(z))
                    l=_f/_g*fg[2];
                else l=_f/_g*limit(fg[2],z,z0,dir);

                if (!is_a<infinity>(z0) and is_number(_f) and is_number(_g)) {
                    if(_f.info(info_flags::real))
                        _fsign=(f.subs(z==z0-pow(10.0,-((long)Digits))).evalf()).info(info_flags::positive)?1:-1;
                    if(_g.info(info_flags::real))
                        _gsign=(g.subs(z==z0-pow(10.0,-((long)Digits))).evalf()).info(info_flags::positive)?1:-1;
                }
                numeric sign = _fsign/_gsign;

                if ((l.info(info_flags::positive) and sign.is_negative())
                    || (l.info(info_flags::negative) and sign.is_positive())) {
                    l= l*sign;
                }
            }

        } catch (...) {
            try {
                if(dir=="-"){
                    l= limit_by_series(expr,z,z0,dir);
                    if(!fg[2].has(z))
                        l=l*fg[2];
                    else l=l*limit(fg[2],z,z0,dir);

                    r=l;
                }
            } catch (...) {
                l= Limit(e,z,z0,dir);
            }
        }
    }

    if (dir=="+-") {
        if (r==l){
            if (is_exponential_indeterminate_form) {
                return exponential_indeterminate_const_multerm*exp(r);
            }
            else return r;
        }

        else
            return Limit(e,z,z0,dir);
    }
    else if(dir=="+"){
        if (is_exponential_indeterminate_form) {
            return exponential_indeterminate_const_multerm*exp(r);
        }
        else return r;
    }
    else {
        if (is_exponential_indeterminate_form) {
            return exponential_indeterminate_const_multerm*exp(l);
        }
        else return l;
    }

}
}
