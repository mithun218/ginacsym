/** @file time_gammaseries.cpp
 *
 *  Some timings on series expansion of the Gamma function around a pole. */

/*
 *  GiNaC Copyright (C) 1999-2023 Johannes Gutenberg University Mainz, Germany
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

#include "ginacsym.h"
#include "timer.h"
using namespace ginacsym;

#include <iostream>
#include <vector>
using namespace std;

unsigned tgammaseries(unsigned order)
{
	unsigned result = 0;
	symbol x;

	ex myseries = series(ginacsym::tgamma(x),x==0,order);
	// compute the last coefficient numerically:
	ex last_coeff = myseries.coeff(x,order-1).evalf();
	// compute a bound for that coefficient using a variation of the leading
	// term in Stirling's formula:
	ex bound = exp(-.57721566490153286*(order-1))/(order-1);
	if (abs((last_coeff-pow(-1,ex(order)))/bound) > 1) {
		clog << "The " << order-1
		     << "th order coefficient in the power series expansion of tgamma(0) was erroneously found to be "
		     << last_coeff << ", violating a simple estimate." << endl;
		++result;
	}

	return result;
}

unsigned time_gammaseries()
{
	unsigned result = 0;

	cout << "timing Laurent series expansion of Gamma function" << flush;

	vector<unsigned> sizes = {20, 25, 30, 35};
	vector<double> times;
	timer omega;

	for (vector<unsigned>::iterator i=sizes.begin(); i!=sizes.end(); ++i) {
		omega.start();
		result += tgammaseries(*i);
		times.push_back(omega.read());
		cout << '.' << flush;
	}

	// print the report:
	cout << endl << "	order: ";
	for (vector<unsigned>::iterator i=sizes.begin(); i!=sizes.end(); ++i)
		cout << '\t' << *i;
	cout << endl << "	time/s:";
	for (vector<double>::iterator i=times.begin(); i!=times.end(); ++i)
		cout << '\t' << *i;
	cout << endl;
	
	return result;
}

extern void randomify_symbol_serials();

int main(int argc, char** argv)
{
	randomify_symbol_serials();
	cout << setprecision(2) << showpoint;
	return time_gammaseries();
}
