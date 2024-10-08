/** @file relational.cpp
 *
 *  Implementation of relations between expressions */

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

#include "relational.h"
#include "infinity.h"
#include "operators.h"
#include "numeric.h"
#include "archive.h"
#include "utils.h"
#include "hash_seed.h"
#include "compiler.h"
#include "symbol.h"

#include <stdexcept>

namespace ginacsym {

GINAC_IMPLEMENT_REGISTERED_CLASS_OPT(relational, basic,
  print_func<print_context>(&relational::do_print).
  print_func<print_latex>(&relational::do_print_latex).
  print_func<print_tree>(&relational::do_print_tree).
  print_func<print_python_repr>(&relational::do_print_python_repr))

//////////
// default constructor
//////////

relational::relational() { }

//////////
// other constructors
//////////

// public

relational::relational(const ex & lhs, const ex & rhs, operators oper) :
	lh(lhs), rh(rhs), o(oper) { }

//////////
// archiving
//////////

void relational::read_archive(const archive_node& n, lst& sym_lst)
{
	inherited::read_archive(n, sym_lst);
	unsigned int opi;
	if (!(n.find_unsigned("op", opi)))
		throw (std::runtime_error("unknown relational operator in archive"));
	o = (operators)opi;
	n.find_ex("lh", lh, sym_lst);
	n.find_ex("rh", rh, sym_lst);
}
GINAC_BIND_UNARCHIVER(relational);

void relational::archive(archive_node &n) const
{
	inherited::archive(n);
	n.add_ex("lh", lh);
	n.add_ex("rh", rh);
	n.add_unsigned("op", o);
}

//////////
// functions overriding virtual functions from base classes
//////////

// public

static void print_operator(const print_context & c, relational::operators o)
{
	switch (o) {
	case relational::equal:
		c.s << "==";
		break;
	case relational::not_equal:
		c.s << "!=";
		break;
	case relational::less:
		c.s << "<";
		break;
	case relational::less_or_equal:
		c.s << "<=";
		break;
	case relational::greater:
		c.s << ">";
		break;
	case relational::greater_or_equal:
		c.s << ">=";
		break;
	default:
		c.s << "(INVALID RELATIONAL OPERATOR)";
		break;
	}
}

static void print_latex_operator(const print_context & c, relational::operators o)
{
    switch (o) {
    case relational::equal:
        c.s << "==";
        break;
    case relational::not_equal:
        c.s << "\\neq";
        break;
    case relational::less:
        c.s << "<";
        break;
    case relational::less_or_equal:
        c.s << "\\leq";
        break;
    case relational::greater:
        c.s << ">";
        break;
    case relational::greater_or_equal:
        c.s << "\\geq";
        break;
    default:
        c.s << "(INVALID RELATIONAL OPERATOR)";
        break;
    }
}

void relational::do_print_latex(const print_latex & c, unsigned level) const
{
    if (precedence() <= level)
        c.s << "(";
    lh.print(c, precedence());
    print_latex_operator(c, o);
    rh.print(c, precedence());
    if (precedence() <= level)
        c.s << ")";
}

void relational::do_print(const print_context & c, unsigned level) const
{
	if (precedence() <= level)
		c.s << "(";
	lh.print(c, precedence());
	print_operator(c, o);
	rh.print(c, precedence());
	if (precedence() <= level)
		c.s << ")";
}

void relational::do_print_python_repr(const print_python_repr & c, unsigned level) const
{
	c.s << class_name() << '(';
	lh.print(c);
	c.s << ',';
	rh.print(c);
	c.s << ",'";
	print_operator(c, o);
	c.s << "')";
}

bool relational::info(unsigned inf) const
{
	switch (inf) {
		case info_flags::relation:
			return 1;
		case info_flags::relation_equal:
			return o==equal;
		case info_flags::relation_not_equal:
			return o==not_equal;
		case info_flags::relation_less:
			return o==less;
		case info_flags::relation_less_or_equal:
			return o==less_or_equal;
		case info_flags::relation_greater:
			return o==greater;
		case info_flags::relation_greater_or_equal:
			return o==greater_or_equal;
	}
	return 0;
}

size_t relational::nops() const
{
	return 2;
}

ex relational::op(size_t i) const
{
	GINAC_ASSERT(i<2);

	return i==0 ? lh : rh;
}

ex relational::map(map_function & f) const
{
    const ex &mapped_lh = f.expr_visitor(lh);
    const ex &mapped_rh = f.expr_visitor(rh);

	if (!are_ex_trivially_equal(lh, mapped_lh)
	 || !are_ex_trivially_equal(rh, mapped_rh))
		return dynallocate<relational>(mapped_lh, mapped_rh, o);
	else
		return *this;
}

ex relational::subs(const exmap & m, unsigned options) const
{
	const ex & subsed_lh = lh.subs(m, options);
	const ex & subsed_rh = rh.subs(m, options);

	if (!are_ex_trivially_equal(lh, subsed_lh) || !are_ex_trivially_equal(rh, subsed_rh))
		return relational(subsed_lh, subsed_rh, o).subs_one_level(m, options);
	else
		return subs_one_level(m, options);
}

ex relational::eval_ncmul(const exvector & v) const
{
	return lh.eval_ncmul(v);
}

// protected

int relational::compare_same_type(const basic & other) const
{
	GINAC_ASSERT(is_exactly_a<relational>(other));
	const relational &oth = static_cast<const relational &>(other);
	if (o==oth.o && lh.is_equal(oth.lh) && rh.is_equal(oth.rh))
		return 0;
	switch (o) {
		case equal:
		case not_equal:
			if (oth.o!=o)
				return (o < oth.o) ? -1 : 1;
			break;
		case less:
			if (oth.o!=greater)
				return (o < oth.o) ? -1 : 1;
			break;
		case less_or_equal:
			if (oth.o!=greater_or_equal)
				return (o < oth.o) ? -1 : 1;
			break;
		case greater:
			if (oth.o!=less)
				return (o < oth.o) ? -1 : 1;
			break;
		case greater_or_equal:
			if (oth.o!=less_or_equal)
				return (o < oth.o) ? -1 : 1;
			break;
	}
	const int lcmpval = lh.compare(oth.lh);
	return (lcmpval!=0) ? lcmpval : rh.compare(oth.rh);
}

bool relational::match_same_type(const basic & other) const
{
	GINAC_ASSERT(is_exactly_a<relational>(other));
	const relational &oth = static_cast<const relational &>(other);

	return o == oth.o;
}

unsigned relational::return_type() const
{
	GINAC_ASSERT(lh.return_type()==rh.return_type());
	return lh.return_type();
}

return_type_t relational::return_type_tinfo() const
{
	GINAC_ASSERT(lh.return_type_tinfo()==rh.return_type_tinfo());
	return lh.return_type_tinfo();
}

unsigned relational::calchash() const
{
	unsigned v = make_hash_seed(typeid(*this));
	unsigned lhash = lh.gethash();
	unsigned rhash = rh.gethash();

	v = rotate_left(v);
	switch(o) {
		case equal:
		case not_equal:
			if (lhash>rhash) {
				v ^= lhash;
				lhash = rhash;
			} else {
				v ^= rhash;
			}
			break;
		case less:
		case less_or_equal:
			v ^= rhash;
			break;
		case greater:
		case greater_or_equal:
			v ^= lhash;
			lhash = rhash;
			break;
	}
	v = rotate_left(v);
	v ^= lhash;

	// store calculated hash value only if object is already evaluated
	if (flags & status_flags::evaluated) {
		setflag(status_flags::hash_calculated);
		hashvalue = v;
	}

	return v;
}

//////////
// new virtual functions which can be overridden by derived classes
//////////

// none

//////////
// non-virtual functions in this class
//////////

relational::safe_bool relational::make_safe_bool(bool cond) const
{
	return cond? &safe_bool_helper::nonnull : nullptr;
}

/** Cast the relational into a Boolean, mainly for evaluation within an
 *  if-statement.  Note that (a<b) == false does not imply (a>=b) == true in
 *  the general symbolic case.  A false result means the comparison is either
 *  false or undecidable (except of course for !=, where true means either
 *  unequal or undecidable). */
relational::operator relational::safe_bool() const
{
	const ex df = lh-rh;  // like ::canonical() method
	// We treat numeric and symbolic expression differently
	if (is_exactly_a<numeric>(df)) {
		switch (o) {
			case equal:
				return make_safe_bool(ex_to<numeric>(df).is_zero());
			case not_equal:
				return make_safe_bool(!ex_to<numeric>(df).is_zero());
			case less:
				return make_safe_bool(ex_to<numeric>(df)<(*_num0_p));
			case less_or_equal:
				return make_safe_bool(ex_to<numeric>(df)<=(*_num0_p));
			case greater:
				return make_safe_bool(ex_to<numeric>(df)>(*_num0_p));
			case greater_or_equal:
				return make_safe_bool(ex_to<numeric>(df)>=(*_num0_p));
			default:
				throw(std::logic_error("invalid relational operator"));
		}
	} else {
		// The conversion for symbolic expressions is based on the info flags
		switch (o) {
			case equal:
				return make_safe_bool(df.is_zero());
			case not_equal:
				return make_safe_bool(! df.is_zero());
			case less:
				return make_safe_bool(df.info(info_flags::negative));
			case less_or_equal:
				return make_safe_bool((-df).info(info_flags::nonnegative));
			case greater:
				return make_safe_bool(df.info(info_flags::positive));
			case greater_or_equal:
				return make_safe_bool(df.info(info_flags::nonnegative));
			default:
				throw(std::logic_error("invalid relational operator"));
		}
	}
}

/** Returns an equivalent relational with zero right-hand side.
 */
ex relational::canonical() const
{
	return relational(lh-rh, _ex0, o);
}


static relational::operators flip(relational::operators op);

static relational::operators flip(relational::operators op)
{
    switch (op) {
    case relational::equal:
    case relational::not_equal:
        return op;
    case relational::less:
        return relational::greater;
    case relational::less_or_equal:
        return relational::greater_or_equal;
    case relational::greater:
        return relational::less;
    case relational::greater_or_equal:
        return relational::less_or_equal;
    default:
        throw(std::logic_error("invalid relational operator"));
    }
}

relational::result relational::decide() const
{
    if (unlikely(is_a<infinity>(rh) and is_a<infinity>(lh))) {
        const infinity & lh_inf = ex_to<infinity>(lh);
        const infinity & rh_inf = ex_to<infinity>(rh);
        const ex df = lh_inf.get_sign() - rh_inf.get_sign();

        if (!is_exactly_a<numeric>(df))
            return result::notimplemented;

        switch (o) {
        case equal:
            if (ex_to<numeric>(df).is_zero())
                return result::True;
            else
                return result::False;
        case not_equal:
            if (ex_to<numeric>(df).is_zero())
                return result::False;
            else
                return result::True;
        case less:
        case less_or_equal:
            if (lh_inf.info(info_flags::negative) and rh_inf.info(info_flags::positive))
                return result::True;
            else
                return result::False;
        case greater:
        case greater_or_equal:
            if (lh_inf.info(info_flags::positive) and rh_inf.info(info_flags::negative))
                return result::True;
            else
                return result::False;
        default:
            throw(std::logic_error("invalid relational operator"));
        }
        return result::notimplemented;
    }

    if (unlikely(is_a<infinity>(lh)) or unlikely(is_a<infinity>(rh))) {
        infinity inf;
        ex other = rh;
        operators oper = o;
        if (unlikely(is_a<infinity>(rh))) {
            other = lh;
            inf = ex_to<infinity>(rh);
            oper = flip(o);
        }
        else {
            inf = ex_to<infinity>(lh);
        }
        if (inf.info(info_flags::positive) and o!=equal and o!=not_equal)
            return result::undecidable;
        if (has_symbol(other))
            return result::notimplemented;
        if (inf.compare_other_type(other, oper))
            return result::True;

        return result::False;
    }

    const ex df = lh-rh;
    if (!is_exactly_a<numeric>(df)) {
        switch (o) {
        case equal:
            if (!df.is_equal(_ex0))
                return result::False;
            else if (df.is_zero())
                return result::True;
            else
                return result::notimplemented;
        case not_equal:
            if (!df.is_equal(_ex0))
                return result::True;
            else if (df.is_zero())
                return result::False;
            else
                return result::notimplemented;
        case less:
            if ((-df).info(info_flags::positive))
                return result::True;
            else if(df.info(info_flags::nonnegative))
                return result::False;
            else
                return result::notimplemented;
        case greater:
            if (df.info(info_flags::positive))
                return result::True;
            else if(df.is_zero()
                     or (-df).info(info_flags::positive))
                return result::False;
            else
                return result::notimplemented;
        case less_or_equal:
            if (df.is_zero() or (-df).info(info_flags::positive))
                return result::True;
            else if (df.info(info_flags::positive))
                return result::False;
            else
                return result::notimplemented;
        case greater_or_equal:
            if (df.is_zero() or df.info(info_flags::positive))
                return result::True;
            else if(df.info(info_flags::negative))
                return result::False;
            else
                return result::notimplemented;
        default:
            throw(std::logic_error("invalid relational operator"));
        }
        return result::notimplemented;
    }

    switch (o) {
    case equal:
        if (ex_to<numeric>(df).is_zero())
            return result::True;
        else
            return result::False;
    case not_equal:
        if (!ex_to<numeric>(df).is_zero())
            return result::True;
        else
            return result::False;
    case less:
        if (ex_to<numeric>(df) < (*_num0_p))
            return result::True;
        else
            return result::False;
    case less_or_equal:
        if (ex_to<numeric>(df) <= (*_num0_p))
            return result::True;
        else
            return result::False;
    case greater:
        if (ex_to<numeric>(df) > (*_num0_p))
            return result::True;
        else
            return result::False;
    case greater_or_equal:
        if (ex_to<numeric>(df) >= (*_num0_p))
            return result::True;
        else
            return result::False;
    default:
        throw(std::logic_error("invalid relational operator"));
    }
}

} // namespace ginacsym
