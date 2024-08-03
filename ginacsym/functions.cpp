/** @file functions.cpp
 *
 *  Implementation of class functions. */

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

#include "ex.h"
#include "functions.h"
#include "operators.h"

namespace ginacsym{

GINAC_IMPLEMENT_REGISTERED_CLASS_OPT(functions, basic,
                                     print_func<print_context>(&functions::do_print).
                                     print_func<print_latex>(&functions::do_print_latex))

functions::functions(){}
functions::functions(const std::string &fns_, const lst &fd_, unsigned assu){

    fns=(fns_);functiondependency=(fd_); assumption=(assu);
    std::ostringstream tem;

    if(*fns.begin()=='\\'){
        tem << fns_.substr(1,fns.npos-1) << "(";
        islatexname=true;
    }
    else{
        tem << fns_ << "(";
        islatexname=false;
    }
    for (size_t i = 0; i < (fd_).nops(); i++) {
        if (i != 0)
            tem << "," << (fd_[i]);
        else
            tem << fd_[i];
    }
    tem << ")";

    functionname = generator.functionSymbolFromString(tem.str(),assu);

}

int functions::compare_same_type(const basic & other) const
{
    GINAC_ASSERT(is_exactly_a<functions>(other));
    const functions &oth = static_cast<const functions &>(other);
    return functionname.compare(oth.functionname);
}

ex functions::subs(const exmap& m, unsigned options) const
{
    for (auto it=m.begin(); it!=m.end();it++) {
        if (it->first.is_equal(*this)) {
            return it->second;
        }
    }
    return *this;
}

bool functions::info(unsigned inf) const
{
    switch (inf) {
    case info_flags::real:
        if(assumption==symbol_assumptions::realsymbol ||
           assumption==symbol_assumptions::possymbol )
            return 1;
        break;
    case info_flags::positive:
        if(assumption==symbol_assumptions::possymbol)
            return 1;
        break;
    }
    return 0;
}

}

