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
#include "inert.h"
#include "inifcns.h"
#include "wildcard.h"


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

//It replace Diff_helper, Integrate_helper to Diff, Integrate
class replace_extented_classc: public map_function{
public:
    replace_extented_classc(){}
    ex expr_visitor(const ex& e){
        if(is_ex_the_function(e,Diff_helper)){
            return Diff(e.op(0),e.op(1),e.op(2));
        }
        else if(is_ex_the_function(e,Integrate_helper)){
            return Integrate(e.op(0),e.op(1));
        }
        else return e.map(*this);
    }
};
replace_extented_classc replace_extented_class;
//This will generate ex and also create the missing symbols
ex generatorc::exGenerator(const std::string& s_, unsigned symboltype, const bool& islatexname)
{
    try{
        std::string s=s_;
        //Enabling parsing of some extended classes, such as Diff,Integrate
        //list of classes at the begining of expression
        std::vector<std::string> classListBegin ={"Diff(","Integrate("};
        for (int var = 0; var < classListBegin.size(); ++var) {
            std::string bstring=s.substr(0,classListBegin[var].size());
            if ((bstring)==classListBegin[var]) {
                bstring = bstring.substr(0,bstring.size()-1);
                s.replace(0,bstring.size(),bstring+"_helper");
            }
        }
        //list of classes inside expressions
        std::vector<std::string> classListInside = {"(Diff(","+Diff(","-Diff(","*Diff(","/Diff(","^Diff(",
                                              "(Integrate(","+Integrate(","-Integrate(","*Integrate(","/Integrate(","^Integrate("};
        for (int var = 0; var < classListInside.size(); ++var) {
            size_t pos=s.find(classListInside[var]);
            while (pos!=std::string::npos) {
                std::string newString=classListInside[var].substr(0,classListInside[var].size()-1)+"_helper";
                s.replace(pos,classListInside[var].size()-1,newString);
                pos=s.find(classListInside[var],pos+newString.size()+1);
            }
        }

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
        if(s==s_)
            return reader1(s);
        else{
            return replace_extented_class.expr_visitor(reader1(s));
        }
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

