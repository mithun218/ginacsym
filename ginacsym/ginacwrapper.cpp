/** @file ginacwrapper.cpp
 *
 *  Implementation of some wrapper functions for cython wrapping. */

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

#include "ginacwrapper.h"
#include "parser.h"
#include "symbol.h"



namespace ginacsym {

std::ostringstream strstr,latexstr,pythonstr;
//std::map<std::string, ex> generatorc::symboldirectory;
//std::map<std::string,unsigned> generatorc::symboltypes;
ex& generatorc::symGenerator(const std::string& s, unsigned symboltype, const bool& islatexname)
{
    std::map<std::string, ex>::iterator i = symboldirectory.find(s);
    if (i != symboldirectory.end()){// symbol is aready present
        if(symboltypes[i->first]==symboltype)// symboltype is same
            return i->second;
        else{//update symboldirectory and symboltypes
            symboltypes[i->first]=symboltype;
            if(!islatexname){
                if(symboltype==symbol_assumptions::symbol){
                    symboldirectory[i->first]=symbol(s);
                    return symboldirectory.at(i->first);
                }
                else if(symboltype==symbol_assumptions::realsymbol){
                    symboldirectory[i->first]=realsymbol(s);
                    return symboldirectory.at(i->first);
                }
                else if(symboltype==symbol_assumptions::possymbol){
                    symboldirectory[i->first]=possymbol(s);
                    return symboldirectory.at(i->first);
                }
                else throw ginacsym::unsupported_symbol();
            }
            else{
                if(symboltype==symbol_assumptions::symbol){
                    symboldirectory[i->first]=symbol(s,"\\"+s);
                    return symboldirectory.at(i->first);
                }
                else if(symboltype==symbol_assumptions::realsymbol){
                    symboldirectory[i->first]=realsymbol(s,"\\"+s);
                    return symboldirectory.at(i->first);
                }
                else if(symboltype==symbol_assumptions::possymbol){
                    symboldirectory[i->first]=possymbol(s,"\\"+s);
                    return symboldirectory.at(i->first);
                }
                else throw ginacsym::unsupported_symbol();
            }
        }
    }
    else{//insert new symbol and symboltypes
        symboltypes.insert(make_pair(s, symboltype));
        if(!islatexname){
            if (symboltype==symbol_assumptions::symbol)
                return symboldirectory.insert(make_pair(s, symbol(s))).first->second;
            else if(symboltype==symbol_assumptions::realsymbol)
                return symboldirectory.insert(make_pair(s, realsymbol(s))).first->second;
            else if (symboltype==symbol_assumptions::possymbol)
                return symboldirectory.insert(make_pair(s, possymbol(s))).first->second;
            else throw ginacsym::unsupported_symbol();
        }
        else{
            if (symboltype==symbol_assumptions::symbol)
                return symboldirectory.insert(make_pair(s, symbol(s,"\\"+s))).first->second;
            else if(symboltype==symbol_assumptions::realsymbol)
                return symboldirectory.insert(make_pair(s, realsymbol(s,"\\"+s))).first->second;
            else if (symboltype==symbol_assumptions::possymbol)
                return symboldirectory.insert(make_pair(s, possymbol(s,"\\"+s))).first->second;
            else throw ginacsym::unsupported_symbol();
        }
    }
    throw ginacsym::unsupported_symbol();
}

//This will generate ex and also create the missing symbols
ex generatorc::exGenerator(const std::string& s, unsigned symboltype, const bool& islatexname)
{
    try{
        if (symboldirectory.find(s)!=symboldirectory.end()){//s is symbol and aready present
            if(symboltypes[s]!=symboltype){// symboltype is not same
                                            //update symboldirectory and symboltypes
                symboltypes[s]=symboltype;
                if(!islatexname){
                    if(symboltype==symbol_assumptions::symbol){
                        symboldirectory[s]=symbol(s);
                    }
                    else if(symboltype==symbol_assumptions::realsymbol){
                        symboldirectory[s]=realsymbol(s);
                    }
                    else if(symboltype==symbol_assumptions::possymbol){
                        symboldirectory[s]=possymbol(s);
                    }
                    else throw ginacsym::unsupported_symbol();
                }
                else{
                    if(symboltype==symbol_assumptions::symbol){
                        symboldirectory[s]=symbol(s,"\\"+s);
                    }
                    else if(symboltype==symbol_assumptions::realsymbol){
                        symboldirectory[s]=realsymbol(s,"\\"+s);
                    }
                    else if(symboltype==symbol_assumptions::possymbol){
                        symboldirectory[s]=possymbol(s,"\\"+s);
                    }
                    else throw ginacsym::unsupported_symbol();
                }
            }
        }

        else{
            reader(s);
            symtab st=reader.get_syms();
            for (symtab::iterator itr = st.begin(); itr != st.end();itr++) {

                //insert new symbol in symboldirectory
                if(symboldirectory.find(itr->first)==symboldirectory.end()){
                    symboltypes.insert(make_pair(itr->first, symboltype));
                    if(!islatexname){
                        if (symboltype==symbol_assumptions::symbol)
                            symboldirectory.insert(make_pair(itr->first, symbol(itr->first)));
                        else if(symboltype==symbol_assumptions::realsymbol)
                            symboldirectory.insert(make_pair(itr->first, realsymbol(itr->first)));
                        else if (symboltype==symbol_assumptions::possymbol)
                            symboldirectory.insert(make_pair(itr->first, possymbol(itr->first)));
                        else throw ginacsym::unsupported_symbol();
                    }
                    else{
                        if (symboltype==symbol_assumptions::symbol)
                            symboldirectory.insert(make_pair(itr->first, symbol(itr->first,"\\"+itr->first)));
                        else if(symboltype==symbol_assumptions::realsymbol)
                            symboldirectory.insert(make_pair(itr->first, realsymbol(itr->first,"\\"+itr->first)));
                        else if (symboltype==symbol_assumptions::possymbol)
                            symboldirectory.insert(make_pair(itr->first, possymbol(itr->first,"\\"+itr->first)));
                        else throw ginacsym::unsupported_symbol();
                    }
                }
            }
        }
        parser reader1(symboldirectory);
        return reader1(s);
    }
    catch(...){ ginacsym::unexpected_error();}
    throw ginacsym::unexpected_error();;
}

ex generatorc::functionSymbolFromString(const std::string& s, unsigned symboltype)
{
    symboltypes[s]=symboltype;

    if(symboltype==symbol_assumptions::symbol){
        symboldirectory[s]=symbol(s);
        return symboldirectory.at(s);
    }
    else if(symboltype==symbol_assumptions::realsymbol){
        symboldirectory[s]=realsymbol(s);
        return symboldirectory.at(s);
    }
    else if(symboltype==symbol_assumptions::possymbol){
        symboldirectory[s]=possymbol(s);
        return symboldirectory.at(s);
    }
    else throw ginacsym::unsupported_symbol();
}


//This will register externally created symbol
int generatorc::symRegister(const ex& syms)
{
    symboldirectory[to_string(syms)]=syms;
    if(syms.info(info_flags::real))
        symboltypes[to_string(syms)]=symbol_assumptions::realsymbol;
    else if(syms.info(info_flags::positive))
        symboltypes[to_string(syms)]=symbol_assumptions::possymbol;
    else
        symboltypes[to_string(syms)]=symbol_assumptions::symbol;

    return 0;
}

//This will generate ex, but does not create the missing symbols
ex generatorc::exGeneratorFromString(const std::string& s) const
{
    parser reader1(symboldirectory);
    return reader1(s);
}

//returning all symbols with assumptions by symbolinfo argument
std::map<ex,unsigned,ex_is_less> generatorc::allinfo() const
{
    std::map<ex,unsigned,ex_is_less> symbolinfo;
    for (symtab::const_iterator itr = symboldirectory.begin(); itr != symboldirectory.end();itr++){
        symbolinfo.insert(std::make_pair(itr->second,symboltypes.at(itr->first)));
    }
    return symbolinfo;
}

//returning a symbol with assumption
std::map<ex,unsigned,ex_is_less> generatorc::aninfo(const ex& e) const
{
    std::map<ex,unsigned,ex_is_less> symbolinfo;
    const std::string str=to_string(e);
    symbolinfo.insert(std::make_pair(symboldirectory.at(str),symboltypes.at(str)));
    return symbolinfo;
}

generatorc generator;

externSymbolsc::externSymbolsc(){
    symb_=generator.symGenerator("symb_");
    factSymb_=generator.symGenerator("factSymb_");
    nan=generator.symGenerator("nan");
}
externSymbolsc externSymbols;

}

