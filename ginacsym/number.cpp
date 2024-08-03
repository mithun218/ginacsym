#include "ex.h"
#include "number.h"
#include "flint/fmpz.h"
#include "ginacwrapper.h"
#include "utils.h"
#include <cln/integer.h>
#include <cln/integer_io.h>
#include <cln/numtheory.h>

namespace ginacsym {

flint_variablec flint_variable;
//the digits of n in base b
std::string base_form(const ex& n, const int& b)
{
    if (!n.info(info_flags::integer))
        throw std::invalid_argument("ex object is not integer.");

//    fmpz_t x;
//    fmpz_init(x);
//    fmpz_set_str(x,n,10);
//    const char* str=fmpz_get_str(NULL,b,x);
//    fmpz_clear(x);
//    return str;
    fmpz_set_str(flint_variable.fmpz_1,to_string(n).c_str(),10);
    const char* str=fmpz_get_str(NULL,b,flint_variable.fmpz_1);
    return str;
}

//test whether m is divisible by n
bool divisible(const ex& m, const ex& n)
{
    if (!m.info(info_flags::integer) || !n.info(info_flags::integer))
        throw std::invalid_argument("ex object is not integer.");
//    fmpz_t x,y;
//    fmpz_init(x);
//    fmpz_init(y);
//    fmpz_set_str(x,to_string(m).c_str(),10);
//    fmpz_set_str(y,to_string(n).c_str(),10);
//    const bool isdiv=fmpz_divisible(x,y);
//    fmpz_clear(x);
//    fmpz_clear(y);
//    return isdiv;
    fmpz_set_str(flint_variable.fmpz_1,to_string(m).c_str(),10);
    fmpz_set_str(flint_variable.fmpz_2,to_string(n).c_str(),10);
    const bool isdiv=fmpz_divisible(flint_variable.fmpz_1,flint_variable.fmpz_2);
    return isdiv;
}


//next small prime number of n
ex next_prime(const ex& n)
{
    if (!n.info(info_flags::integer))
        throw std::invalid_argument("ex object is not integer.");
//    fmpz_t x,y;
//    fmpz_init(x);
//    fmpz_init(y);
//    fmpz_set_str(y,to_string(n).c_str(),10);
//    fmpz_nextprime(x,y,1);
//    const char* str=fmpz_get_str(NULL,10,x);
//    fmpz_clear(x);
//    fmpz_clear(y);
//    return numeric(str);
    fmpz_set_str(flint_variable.fmpz_2,to_string(n).c_str(),10);
    fmpz_nextprime(flint_variable.fmpz_1,flint_variable.fmpz_2,1);
    const char* str=fmpz_get_str(NULL,10,flint_variable.fmpz_1);
    return numeric(str);
}

//random number generator
//n must be an integer > 0. This function returns a random integer x in the range 0 <= x < n.
ex random(const ex& n)
{
    if (!n.info(info_flags::integer))
        throw std::invalid_argument("ex object is not integer.");
    return numeric(cln::random_I((cln::cl_I(to_string(n).c_str()))));
}

//random prime generator less than and equal to n
ex random_prime(const ex& n)
{
    if (!n.info(info_flags::integer))
        throw std::invalid_argument("ex object is not integer.");
    if (n<2) {
       throw std::invalid_argument("There are no primes in the specified interval.");
    }

    cln::cl_I nnum= cln::cl_I(to_string(n).c_str());
    cln::cl_I rannum= cln::random_I((nnum));
    rannum=cln::nextprobprime(rannum);
    if(rannum<=nnum) return numeric(rannum);
    else return _ex2;
}

}
