/** @file inifcns_integral.cpp
 *
 *  Implementation of integral functions.
 *
 *  (C) 2024 Mithun Bairagi <bairagirasulpur@gmail.com>
 */


#include "ginacwrapper.h"
#include "inifcns.h"
#include "ex.h"
#include "numeric.h"
#include "power.h"
#include "operators.h"
#include "utility.h"
#include "utils.h"

#include "flint/acb.h"
#include "flint/acb_hypgeom.h"

namespace ginacsym {

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



}
