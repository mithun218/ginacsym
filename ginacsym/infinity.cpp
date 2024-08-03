/** @file infinity.cpp
 *
 *  Implementation of PyNaC's "infinity". */

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

#include "utils.h"
#include "infinity.h"
#include "operators.h"


namespace ginacsym {

GINAC_IMPLEMENT_REGISTERED_CLASS_OPT(infinity, basic,
  print_func<print_context>(&infinity::do_print).
  print_func<print_latex>(&infinity::do_print_latex))


//////////
// default constructor
//////////

// public

infinity::infinity(){sign=_ex1;}

void infinity::set_sign(const ex& new_sign)
{
    sign=new_sign;
}

int infinity::compare_same_type(const basic & other) const
{
    GINAC_ASSERT(is_exactly_a<infinity>(other));
    const infinity &o = static_cast<const infinity &>(other);
    return sign.compare(o.sign);
}


bool infinity::compare_other_type(const ex & other,
                                  relational::operators o) const
{
    const ex& e = other.evalf();
    if (not is_exactly_a<numeric>(e))
        return false;
    const numeric& num = ex_to<numeric>(e);
    if (num.imag() > 0)
        return false;
    switch (o) {
    case relational::not_equal:
        return true;
    case relational::equal:
        return false;
    case relational::less_or_equal:
    case relational::less:
        return sign==-1;
    default:
        return sign==1;
    }
}

// public

void infinity::do_print(const print_context & c, unsigned level) const
{
    if(sign.is_equal(_ex1)){
        c.s << "Infinity";
    }
    else
        c.s << "-Infinity";
}

void infinity::do_print_latex(const print_latex & c, unsigned level) const
{
    if(sign.is_equal(_ex1))
        c.s << "\\infty";
    else
        c.s << "-\\infty";
}


bool infinity::info(unsigned inf) const
{
        switch (inf) {
            case info_flags::real:
                return true;
            case info_flags::positive:
                if(sign.is_equal(_ex1))
                    return true;
                break;
                //else  return false;
            case info_flags::negative:
                if(sign.is_equal(_ex_1))
                    return true;
                break;
            default:
                return false;
        }

            return false;


}


ex infinity::conjugate() const
{
    return *this;
}

ex infinity::real_part() const
{
    return *this;
}

ex infinity::imag_part() const
{
    return *this;
}

// protected

ex infinity::derivative(const symbol & /*s*/) const
{
	return _ex0;
}



infinity infinity::operator *= (const ex & rhs)
{
    if (rhs.info(info_flags::negative)) {
        sign=-sign;
        return *this;
//return dynallocate<infinity>(infinity(_ex_1).hold());
    }
    else if (rhs.info(info_flags::positive)) {
        return *this;
        //return dynallocate<infinity>(infinity(_ex_1).hold());
    }
    else if (rhs.is_zero()){
        throw(indeterminate_error("indeterminate expression: "
                     "0 * infinity encountered."));
    }
//    else {
//        return ex_to<basic>((*this)*rhs).hold();
//    }
    throw(indeterminate_error("indeterminate expression: "
                              "f(x) * infinity encountered."));
}


infinity infinity::operator += (const ex & rhs) const
{
    if(is_a<infinity>(rhs) && rhs.info(info_flags::negative)){
        throw(indeterminate_error("indeterminate expression: "
                                 "infinity - infinity encountered."));
    }
    return *this;
}


//////////
// global "infinity" constants
//////////


const infinity Infinity;



} // namespace ginacsym
