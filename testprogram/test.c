/*
 * Stranger
 * Copyright (C) 2013-2014 University of California Santa Barbara.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the  Free Software
 * Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335,
 * USA.
 *
 * Authors: Muath Alkhalaf, Fang Yu
 */

#include <stranger/stranger.h>
#include <stranger/stranger_lib_internal.h>
/*********************************************

 TEST FUNCTION

 *********************************************/

void dfa_init_indices_map_coeffs(int* indices, int* map, int* coeffs,
		int numVars) {
	int i;

	for (i = 0; i < numVars; i++) {
		indices[i] = i;
		indices[i + numVars] = i + numVars;
		map[2 * i] = 2 * i + 1;
		map[2 * i + 1] = 2 * i;
		coeffs[2 * i] = 0;
		coeffs[2 * i + 1] = 0;
	}
}

//a is the automaton
//t is the transition relation
DFA* dfa_forward_image(DFA* a, DFA* t, int* map, int numVars) {
	int i;
	DFA * temp;
	temp = dfaProduct(a, t, dfaAND);
	//dfaPrintVerbose(temp);
	dfaFree(a);
	dfaFree(t);
	a = dfaMinimize(temp);
	dfaFree(temp);
	//indices: even is the current state variable, odd is the next statevariable
	for (i = 0; i < numVars - 1; i++) {
		temp = dfaProject(a, 2 * i);
		printf("\n project away the track %d\n", i);
		//dfaPrintVerbose(temp);
		dfaFree(a);
		a = dfaMinimize(temp);
		dfaFree(temp);
	}
	//dfaPrintVerbose(a);
	temp = dfaProject(a, 2 * numVars - 2);
	dfaFree(a);
	//dfaPrintVerbose(temp);
	dfaReplaceIndices(temp, map);
	//dfaPrintVerbose(temp);
	a = dfaMinimize(temp);
	dfaFree(temp);
	temp = dfaPrefixClose2(a);
	//dfaPrintVerbose(temp);
	dfaFree(a);
	a = dfaMinimize(temp);
	dfaFree(temp);
	return a;
}

void reset_coeffs(int* coeffs, int var) {
	int i;
	for (i = 0; i < 2 * var; i++)
		coeffs[i] = 0;
}

//Implement Construct(a, stmt)
//a is the automaton
//stmt is specified as lhscoeff*lhs = right is the transition relation
DFA* dfa_forward_image_stmt(DFA* input, int lhs, int lhscoeff,
		int* current_coeffs, int constant, int* map, int* indices, int var) {
	int i;
	int* coeffs;
	DFA* a = dfaCopy(input);
	DFA* temp;
	DFA* tran;
	coeffs = (int *) malloc(sizeof(int) * 2 * var);
	reset_coeffs(coeffs, var);
	coeffs[lhs + 1] = lhscoeff;
	for (i = 0; i < var; i++)
		coeffs[2 * i] = current_coeffs[2 * i];

	tran = build_DFA_eq_2sc(2 * var, coeffs, constant, indices);

	temp = dfaProduct(a, tran, dfaAND);
	//  dfaPrintVerbose(temp);
	dfaFree(a);
	dfaFree(tran);
	a = dfaMinimize(temp);
	dfaFree(temp);

	reset_coeffs(coeffs, var);
	for (i = 0; i < var; i++)
		if (i != lhs) {
			coeffs[2 * i] = -1;
			coeffs[2 * i + 1] = 1;
		}
	tran = build_DFA_eq_2sc(2 * var, coeffs, 0, indices);

	temp = dfaProduct(a, tran, dfaAND);
	//  dfaPrintVerbose(temp);
	dfaFree(a);
	dfaFree(tran);
	a = dfaMinimize(temp);
	dfaFree(temp);

	//indices: even is the current state variable, odd is the next statevariable
	for (i = 0; i < var - 1; i++) {
		temp = dfaProject(a, 2 * i);
		//    printf("\n project away the track %d\n", i);
		//    dfaPrintVerbose(temp);
		dfaFree(a);
		a = dfaMinimize(temp);
		dfaFree(temp);
	}
	//dfaPrintVerbose(a);
	temp = dfaProject(a, 2 * var - 2);
	dfaFree(a);
	//  dfaPrintVerbose(temp);
	dfaReplaceIndices(temp, map);
	//  dfaPrintVerbose(temp);
	a = dfaMinimize(temp);
	dfaFree(temp);
	temp = dfaPrefixClose2(a);
	//  dfaPrintVerbose(temp);
	a = dfaMinimize(temp);
	dfaFree(temp);
	return a;
}

//Implement Construct(a, stmt)
//a is the automaton
//Two stmts are specified as lhscoeff*lhs + right +const =0 and lhscoeff2*lhs2 + current_coeffs2 +const2 =0
// is the transition relation

DFA* dfa_forward_image_two_stmt(DFA* input, int lhs, int lhscoeff,
		int* current_coeffs, int constant, int lhs2, int lhscoeff2,
		int* current_coeffs2, int constant2, int* map, int* indices, int var) {
	int i;
	int* coeffs;
	DFA* a = dfaCopy(input);
	DFA* temp;
	DFA* tran;
	coeffs = (int *) malloc(sizeof(int) * 2 * var);

	reset_coeffs(coeffs, var);
	coeffs[lhs + 1] = lhscoeff;
	for (i = 0; i < var; i++)
		coeffs[2 * i] = current_coeffs[2 * i];

	tran = build_DFA_eq_2sc(2 * var, coeffs, constant, indices);

	temp = dfaProduct(a, tran, dfaAND);
	//  dfaPrintVerbose(temp);
	dfaFree(a);
	dfaFree(tran);
	a = dfaMinimize(temp);
	dfaFree(temp);

	reset_coeffs(coeffs, var);
	coeffs[lhs2 + 1] = lhscoeff2;
	for (i = 0; i < var; i++)
		coeffs[2 * i] = current_coeffs2[2 * i];

	tran = build_DFA_eq_2sc(2 * var, coeffs, constant2, indices);

	temp = dfaProduct(a, tran, dfaAND);
	//  dfaPrintVerbose(temp);
	dfaFree(a);
	dfaFree(tran);
	a = dfaMinimize(temp);
	dfaFree(temp);

	reset_coeffs(coeffs, var);
	for (i = 0; i < var; i++)
		if (i != lhs || i != lhs2) {
			coeffs[2 * i] = -1;
			coeffs[2 * i + 1] = 1;
		}
	tran = build_DFA_eq_2sc(2 * var, coeffs, 0, indices);

	temp = dfaProduct(a, tran, dfaAND);
	//  dfaPrintVerbose(temp);
	dfaFree(a);
	dfaFree(tran);
	a = dfaMinimize(temp);
	dfaFree(temp);

	//indices: even is the current state variable, odd is the next statevariable
	for (i = 0; i < var - 1; i++) {
		temp = dfaProject(a, 2 * i);
		//    printf("\n project away the track %d\n", i);
		//    dfaPrintVerbose(temp);
		dfaFree(a);
		a = dfaMinimize(temp);
		dfaFree(temp);
	}
	//dfaPrintVerbose(a);
	temp = dfaProject(a, 2 * var - 2);
	dfaFree(a);
	//  dfaPrintVerbose(temp);
	dfaReplaceIndices(temp, map);
	//  dfaPrintVerbose(temp);
	a = dfaMinimize(temp);
	dfaFree(temp);
	temp = dfaPrefixClose2(a);
	//  dfaPrintVerbose(temp);
	a = dfaMinimize(temp);
	dfaFree(temp);
	return a;
}

//var is equal to the number of string variables + the number of integer variables
void dfa_test_arith(int var) {
	int* indices;
	int* map;
	int* coeffs;
	int constant = 4;

	DFA *a1 = NULL;

	indices = (int *) malloc(sizeof(int) * 2 * var);
	map = (int *) malloc(sizeof(int) * 2 * var);
	coeffs = (int *) malloc(sizeof(int) * 2 * var);

	dfa_init_indices_map_coeffs(indices, map, coeffs, var);

	coeffs[0] = 1;
	coeffs[2] = 2;
	a1 = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	//dfaPrintVerbose(a1);
	reset_coeffs(coeffs, var);
	//  coeffs[1]=1;
	coeffs[2] = -1;
	constant = 0;
	//  a2 = build_DFA_eq_2sc(2*var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	//  dfaPrintVerbose(a2);
	//  a1 = dfa_forward_image(a1, a2, map, var);
	//DFA* dfa_forward_image_stmt(DFA* a, int lhs, int lhscoeff, int* rightcoeffs, int constant, int* map, int* indices, int var)
	a1 = dfa_forward_image_stmt(a1, 0, 1, coeffs, 0, map, indices, var);
	//dfaPrintVerbose(a1);
}

void dfa_test_length(int var, int *indices) {
	DFA *tmp1 = NULL;
	DFA *tmp2 = NULL;
	DFA *tmp3 = NULL;
	DFA *tmp4 = NULL;
	DFA *tmp5 = NULL;
	DFA *tmp6 = NULL;
	DFA *tmp7 = NULL;
	DFA *tmp8 = NULL;
	DFA *tmp9 = NULL;
	DFA *tmp10 = NULL;
	DFA *tmp11 = NULL;
	DFA *uL = NULL;
	DFA *bL = NULL;

	char *c1 = "";
	char *c2 = "k";
	char *c3 = "<ls>\n";
	int i = -1;
	struct semilinear_type* s;

	printf("\n\nTEST WIDEN...............\n");
	tmp1 = dfa_construct_string("ab", var, indices);
	tmp2 = dfa_construct_string("abab", var, indices);
	tmp3 = dfaWiden(tmp1, tmp2);
	//dfaPrintVerbose(tmp3);

	printf("\n\nSTART TESTING...............\n");
	//	printf("\n 1. CONSTRUCT baaab as M1\n");

	tmp1 = dfa_construct_string("baaab", var, indices);
	/*	dfaPrintVerbose(tmp1);

	 printf("\n CONSTRUCT unary DFA  and semilinear set of baaab as M1\n");
	 uL = dfa_string_to_unaryDFA(tmp1, var, indices);
	 dfaPrintVerbose(uL);
	 s=getSemilinerSetCoefficients(uL);
	 print_semilinear_coefficients(s);
	 bL = dfa_semiliner_to_binaryDFA(s);
	 dfaPrintVerbose(bL);
	 dfaFree(uL);
	 dfaFree(bL);
	 free(s);

	 */
	printf("\n 1. (baaab)+\n");
	tmp2 = dfa_closure_extrabit(tmp1, var, indices);
	//dfaPrintVerbose(tmp2);
	uL = dfa_string_to_unaryDFA(tmp2, var, indices);
	printf("\n Unary Length Automaton:\n");
	//dfaPrintVerbose(uL);
	s = getSemilinerSetCoefficients(uL);
	print_semilinear_coefficients(s);
	printf("\n Binary Length Automaton:\n");
	bL = dfa_semiliner_to_binaryDFA(s);
	//dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 2. (baaab)+ab\n");
	tmp3 = dfa_construct_string("ab", var, indices);
	tmp2 = dfa_concat_extrabit(tmp2, tmp3, var, indices);

	uL = dfa_string_to_unaryDFA(tmp2, var, indices);
	printf("\n Unary Length Automaton:\n");
	s = getSemilinerSetCoefficients(uL);
	dfaPrintVerbose(uL);

	print_semilinear_coefficients(s);

	printf("\n Binary Length Automaton:\n");
	bL = dfa_semiliner_to_binaryDFA(s);
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 3. CLOSURE of (baaab)+ab\n");
	tmp4 = dfa_closure_extrabit(tmp2, var, indices);

	uL = dfa_string_to_unaryDFA(tmp4, var, indices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);

	print_semilinear_coefficients(s);

	printf("\n Binary Length Automaton:\n");
	bL = dfa_semiliner_to_binaryDFA(s);
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 4. (abb)+\n");

	tmp3 = dfa_construct_string("abb", var, indices);
	tmp3 = dfa_closure_extrabit(tmp3, var, indices);
	//	dfaPrintVerbose(tmp3);

	uL = dfa_string_to_unaryDFA(tmp3, var, indices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);
	print_semilinear_coefficients(s);
	bL = dfa_semiliner_to_binaryDFA(s);
	printf("\n Binary Length Automaton:\n");
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 5. Union (baaab)+ab and (abb)+\n");

	//tmp3=dfa_construct_string("ab", var, indices);
	tmp4 = dfa_union(tmp2, tmp3);
	uL = dfa_string_to_unaryDFA(tmp4, var, indices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);

	print_semilinear_coefficients(s);

	bL = dfa_semiliner_to_binaryDFA(s);
	printf("\n Binary Length Automaton:\n");
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 6 CLOSURE of (baaab)+ab | (abb)+\n");

	//tmp3=dfa_construct_string("ab", var, indices);
	tmp4 = dfa_closure_extrabit(tmp4, var, indices);
	uL = dfa_string_to_unaryDFA(tmp4, var, indices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);

	print_semilinear_coefficients(s);

	bL = dfa_semiliner_to_binaryDFA(s);
	printf("\n Binary Length Automaton:\n");
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 7. (abcd)+\n");
	tmp3 = dfa_construct_string("abcd", var, indices);
	tmp3 = dfa_closure_extrabit(tmp3, var, indices);
	//	dfaPrintVerbose(tmp3);

	uL = dfa_string_to_unaryDFA(tmp3, var, indices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);

	print_semilinear_coefficients(s);

	bL = dfa_semiliner_to_binaryDFA(s);
	printf("\n Binary Length Automaton:\n");
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 8. CONCAT (baaab)+ab (abcd)+\n");
	tmp4 = dfa_concat_extrabit(tmp2, tmp3, var, indices);
	//	dfaPrintVerbose(tmp4);

	uL = dfa_string_to_unaryDFA(tmp4, var, indices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);

	print_semilinear_coefficients(s);

	bL = dfa_semiliner_to_binaryDFA(s);
	printf("\n Binary Length Automaton:\n");
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 9. UNION (baaab)+ab(abcd)+ and (baaab)+ab\n");
	tmp5 = dfa_union(tmp4, tmp2);
	//	dfaPrintVerbose(tmp5);

	uL = dfa_string_to_unaryDFA(tmp5, var, indices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);

	print_semilinear_coefficients(s);

	bL = dfa_semiliner_to_binaryDFA(s);
	printf("\n Binary Length Automaton:\n");
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 10. CLOSURE of ((baaab)+ab(abcd)+ | (baaab)+ab)\n");
	tmp6 = dfa_closure_extrabit(tmp5, var, indices);
	//	dfaPrintVerbose(tmp6);

	uL = dfa_string_to_unaryDFA(tmp6, var, indices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);
	print_semilinear_coefficients(s);
	bL = dfa_semiliner_to_binaryDFA(s);
	printf("\n Binary Length Automaton:\n");
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf(
			"\n 11. CONCAT ((baaab)+ab(abcd)+ | (baaab)+ab)+ and ((baaab)+ab(abcd)+ | (baaab)+ab)\n");
	tmp7 = dfa_concat_extrabit(tmp6, tmp5, var, indices);
	//	dfaPrintVerbose(tmp7);

	uL = dfa_string_to_unaryDFA(tmp7, var, indices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);
	print_semilinear_coefficients(s);
	bL = dfa_semiliner_to_binaryDFA(s);
	printf("\n Binary Length Automaton:\n");
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 12. Emptiness Checking of 11 \n");
	i = check_emptiness(tmp7, var, indices);
	printf("\n\t Result[-1:unknown, 0:false, 1:true]: %d \n", i);

	printf("\n 13. Equivalence Checking of 10(M+.M) and 9(M+) \n");
	i = -1;
	i = check_equivalence(tmp7, tmp6, var, indices);
	printf("\n\t Result[-1:unknown, 0:false, 1:true]: %d \n", i);

	printf("\n 14. UNION M and (M)+.M\n");
	tmp8 = dfa_union(tmp7, tmp5);
	//	dfaPrintVerbose(tmp8);
	uL = dfa_string_to_unaryDFA(tmp8, var, indices);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);

	s = getSemilinerSetCoefficients(uL);
	print_semilinear_coefficients(s);

	bL = dfa_semiliner_to_binaryDFA(s);
	printf("\n Binary Length Automaton:\n");
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 15. Equivalence Checking on (M u M+.M) and (M+) \n");
	i = -1;
	i = check_equivalence(tmp8, tmp6, var, indices);
	printf("\n\t Result[-1:unknown, 0:false, 1:true]: %d \n", i);

	printf("\n 16. Replace test: deletion \n");
	tmp9 = dfa_replace_extrabit(tmp2, tmp3, c1, var, indices);
	//	dfaPrintVerbose(tmp9);

	uL = dfa_string_to_unaryDFA(tmp9, var, indices);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);

	s = getSemilinerSetCoefficients(uL);
	print_semilinear_coefficients(s);

	bL = dfa_semiliner_to_binaryDFA(s);
	printf("\n Binary Length Automaton:\n");
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 17. Replace test: char \n");
	tmp10 = dfa_replace_extrabit(tmp2, tmp3, c2, var, indices);
	//	dfaPrintVerbose(tmp10);

	uL = dfa_string_to_unaryDFA(tmp10, var, indices);
	s = getSemilinerSetCoefficients(uL);

	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);

	print_semilinear_coefficients(s);

	bL = dfa_semiliner_to_binaryDFA(s);
	printf("\n Binary Length Automaton:\n");
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	printf("\n 18. Replace test: string \n");
	tmp11 = dfa_replace_extrabit(tmp2, tmp3, c3, var, indices);
	//	dfaPrintVerbose(tmp11);

	uL = dfa_string_to_unaryDFA(tmp11, var, indices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);

	print_semilinear_coefficients(s);

	bL = dfa_semiliner_to_binaryDFA(s);
	printf("\n Binary Length Automaton:\n");
	dfaPrintVerbose(bL);
	dfaFree(bL);
	dfaFree(uL);
	free(s);

	//printf("\n\nEquivalence: %d\n\n", dfaEquivalence(tmp1, resultDFA));
	//dfaPrintVerbose(resultDFA);

	printf("free tmp1-8\n");
	dfaFree(tmp1);
	dfaFree(tmp2);
	dfaFree(tmp3);
	dfaFree(tmp4);
	dfaFree(tmp5);
	dfaFree(tmp6);
	dfaFree(tmp7);
	dfaFree(tmp8);
	printf("free tmp9\n");
	if (tmp9 != tmp2)
		dfaFree(tmp9);
	printf("free tmp10\n");
	if (tmp10 != tmp2)
		dfaFree(tmp10);
	printf("free tmp11\n");
	if (tmp11 != tmp2)
		dfaFree(tmp11);

}

void dfa_test_basic(int var, int *indices) {
	DFA *tmp1 = NULL;
	DFA *tmp2 = NULL;
	DFA *tmp3 = NULL;
	DFA *tmp4 = NULL;
	DFA *tmp9 = NULL;
	DFA *tmp10 = NULL;
	DFA *tmp11 = NULL;

	char *c1 = "";
	char *c2 = "k";
	char *c3 = "ddd";

	printf("\n\nSTART TESTING...............\n");
	printf("\n 1. ac\n");

	tmp1 = dfa_construct_string("ac", var, indices);
	tmp1 = dfa_construct_range('a', 'z', var, indices);
	dfaPrintVerbose(tmp1);
	printf("\n 2. (ac)+\n");
	tmp2 = dfa_closure_extrabit(tmp1, var, indices);
	dfaPrintVerbose(tmp2);

	printf("\n 3. b(ac)+b\n");
	tmp3 = dfa_construct_string("b", var, indices);
	tmp4 = dfa_concat_extrabit(tmp3, tmp2, var, indices);
	tmp4 = dfa_concat_extrabit(tmp4, tmp3, var, indices);
	dfaPrintVerbose(tmp4);

	printf("\n 12. Replace(b(ac)+b, ac, '') test: deletion \n");
	tmp9 = dfa_replace_extrabit(tmp4, tmp1, c1, var, indices);
	dfaPrintVerbose(tmp9);

	printf("\n 12.1 Replace(bac+b, ac+, '') test: deletion closure \n");
	tmp9 = dfa_replace_extrabit(tmp4, tmp2, c1, var, indices);
	dfaPrintVerbose(tmp9);

	printf("\n 13. Replace(bac+b, ac, k) test: char \n");
	tmp10 = dfa_replace_extrabit(tmp4, tmp1, c2, var, indices);
	dfaPrintVerbose(tmp10);

	printf("\n 13.1 Replace(bac+b, ac+, k) test: char closure \n");
	tmp10 = dfa_replace_extrabit(tmp4, tmp2, c2, var, indices);
	dfaPrintVerbose(tmp10);

	printf("\n 14. Replace(bac+b, ac, ddd): string \n");
	tmp11 = dfa_replace_extrabit(tmp4, tmp1, c3, var, indices);
	dfaPrintVerbose(tmp11);

	printf("\n 14.1 Replace(bac+b, ac+, ddd): string closure \n");
	tmp11 = dfa_replace_extrabit(tmp4, tmp2, c3, var, indices);
	dfaPrintVerbose(tmp11);

	//printf("\n\nEquivalence: %d\n\n", dfaEquivalence(tmp1, resultDFA));
	//dfaPrintVerbose(resultDFA);

	printf("free tmp1-8\n");
	dfaFree(tmp1);
	dfaFree(tmp2);
	dfaFree(tmp3);
	dfaFree(tmp4);
	/*	dfaFree(tmp5);
	 dfaFree(tmp6);
	 dfaFree(tmp7);
	 dfaFree(tmp8);
	 */
	printf("free tmp9\n");
	if (tmp9 != tmp4)
		dfaFree(tmp9);
	printf("free tmp10\n");
	if (tmp10 != tmp4)
		dfaFree(tmp10);
	printf("free tmp11\n");
	if (tmp11 != tmp4)
		dfaFree(tmp11);

}

/***********************************************************************************************
 Manual Testing Programs
 For real C programs (used in TACAS09)

 ********************************************************************************************************/

/***********************************************************************************************
 //This is the test prorgram for the following c codes
 // simplified version of strlen() in wu_ftp

 unsigned int strlen(char *s){
 char *ptr = s;
 unsigned int cnt =0;
 //a[0], ptr[0]
 while(*ptr ! = '\0'){
 ++ptr;
 ++cnt;
 //fixpoint: ptr = \Sigma^* \wedge ptr.length +cnt = s.length \wedge ptr.length >=0 (\{1+k|k>=0\})
 //a[1], ptr[1]
 }
 assert(cnt==s.length);
 //fixpoint: ptr = {} \wedge ptr.length +cnt = s.length \wedge ptr.length ==0
 //a[2], ptr[2]
 return cnt;
 }



 ********************************************************************************************************/

//var is equal to the number of string variables + the number of integer variables
void dfa_test_strlen() {
	int var = 3;
	DFA* ptr[3]; //string automaton
	DFA* a[3]; //an array of arithmetic automaton

	int i, itr;
	//arithmetic automaton
	int* indices;
	int* map;
	int* coeffs;
	int* coeffs2;
	int constant = 0;
	DFA* atmp = NULL;
	DFA* assert = NULL;
	//string automaton
	int svar = NUM_ASCII_TRACKS;
	int* sindices = allocateAscIIIndexWithExtraBit(NUM_ASCII_TRACKS);
	DFA* stmp = NULL; //for fixed point computation
	DFA* stmpb = NULL; //for branch condition
	int afixflag = 0;
	int sfixflag = 0;

	//semiliner
	DFA* uL = NULL;
	struct semilinear_type* s;

	for (i = 0; i < 3; i++)
		a[i] = NULL;

	indices = (int *) malloc(sizeof(int) * 2 * var);
	map = (int *) malloc(sizeof(int) * 2 * var);
	coeffs = (int *) malloc(sizeof(int) * 2 * var);
	coeffs2 = (int *) malloc(sizeof(int) * 2 * var);

	dfa_init_indices_map_coeffs(indices, map, coeffs, var);

	// 0: ptr.length, 2:s.length, 4:cnt

	reset_coeffs(coeffs, var);
	coeffs[2] = 1;
	coeffs[4] = -1;
	constant = 0;
	assert = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	dfaPrintVerbose(assert);

	// char *ptr = s;
	reset_coeffs(coeffs, var);
	coeffs[0] = 1;
	coeffs[2] = -1;
	//coeffs[4]=-1;
	constant = 0;
	a[0] = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	dfaPrintVerbose(a[0]);

	reset_coeffs(coeffs, var);
	coeffs[4] = 1;
	constant = 0;
	atmp = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	a[0] = dfaMinimize(dfaProduct(a[0], atmp, dfaAND));
	dfaFree(atmp);

	ptr[0] = dfaAllStringASCIIExceptReserveWords(svar, sindices);

	//cnt =0;
	//reset_coeffs(coeffs, var);
	//constant = 0;
	//DFA* dfa_forward_image_stmt(DFA* a, int lhs, int lhscoeff, int* rightcoeffs, int constant, int* map, int* indices, int var)
	//a[0] = dfaMinimize(dfa_forward_image_stmt(a[0], 4, 1, coeffs, 0, map, indices, var));
	dfaPrintVerbose(a[0]);

	//while(*ptr!='\0')
	stmpb = dfaASCIINotNullString(svar, sindices);

	//dfaPrintVerbose(ptr[1]);

	//++ptr

	atmp = dfaCopy(a[0]);
	stmp = dfaCopy(ptr[0]);
	itr = 0;
	while (1) {

		printf("Iteration %d\n", itr);

		if (!sfixflag) {
			//string analysis
			stmp = dfaMinimize(dfaProduct(stmp, stmpb, dfaAND));
			//DFA *dfa_Suffix(DFA *M, int c1, int c2, int var, int *oldindices)
			ptr[1] = dfaMinimize(dfa_Suffix(stmp, 1, 1, svar, sindices));

			ptr[1] = dfaMinimize(dfaProduct(ptr[1], stmp, dfaOR));
			printf("DFA STIRNG OR %d:\n", itr);
			dfaPrintVerbose(ptr[1]);

			stmp = dfaMinimize(dfaWiden(stmp, ptr[1]));

			dfaFree(stmp);
			stmp = ptr[1];

			if (check_inclusion(stmp, ptr[1], 2 * var, indices)) {
				sfixflag = 1;
				dfaFree(ptr[1]);
				ptr[1] = stmp;
				printf("String Reaching a fixed point at %d iteration!\n", itr);
			} else
				dfaFree(ptr[1]);
		}

		if (!afixflag) {
			//arithmetic analysis
			//-ptr'+ptr - 1 = 0; -cnt'+cnt+1 =0;

			reset_coeffs(coeffs, var);
			coeffs[0] = 1;
			constant = -1;
			reset_coeffs(coeffs2, var);
			coeffs2[4] = 1;
			a[1] = dfaMinimize(
					dfa_forward_image_two_stmt(atmp, 0, -1, coeffs, constant, 4,
							-1, coeffs2, 1, map, indices, var));
			printf("DFA Post %d:\n", itr);
			dfaPrintVerbose(a[1]);

			/*
			 //-ptr'+ptr - 1 = 0;

			 reset_coeffs(coeffs, var);
			 coeffs[0] = 1;
			 constant = -1;
			 //DFA* dfa_forward_image_stmt(DFA* a, int lhs, int lhscoeff, int* othercoeffs, int constant, int* map, int* indices, int var)
			 a[1] = dfaMinimize(dfa_forward_image_stmt(atmp, 0, -1, coeffs, constant, map, indices, var));
			 //dfaPrintVerbose(a[1]);

			 //++cnt;
			 //-cnt'+cnt + 1 =0;
			 reset_coeffs(coeffs, var);
			 coeffs[4] = 1;
			 constant = 1;
			 //DFA* dfa_forward_image_stmt(DFA* a, int lhs, int lhscoeff, int* rightcoeffs, int constant, int* map, int* indices, int var)
			 a[1] = dfaMinimize(dfa_forward_image_stmt(a[1], 4, -1, coeffs, constant, map, indices, var));
			 //a[1] = dfaMinimize(dfa_forward_image_two_stmt(atmp, 0, -1, coeffs, constant, 4, -1, coeffs2, 1, map, indices, var));
			 printf("DFA Post %d:\n", itr);
			 dfaPrintVerbose(a[1]);
			 */

			// alternative for forward_image

			//alternative for widening
			//atmp = dfaProduct(a[1], atmp, dfaOR);
			a[1] = dfaMinimize(dfaProduct(a[1], atmp, dfaOR));
			printf("DFA OR %d:\n", itr);
			dfaPrintVerbose(a[1]);

			atmp = dfaMinimize(dfaWiden(atmp, a[1]));
			//atmp = dfaMinimize(dfaWiden(a[1], atmp));
			printf("DFA Widen %d:\n", itr);
			dfaPrintVerbose(atmp);

			if (check_inclusion(atmp, a[1], 2 * var, indices)) {
				afixflag = 1;
				dfaFree(a[1]);
				a[1] = atmp;
				printf("Arith Reaching a fixed point at %d iteration!\n", itr);
			} else {
				dfaFree(a[1]);
			}
		}

		if (afixflag && sfixflag)
			break;
		else {
			itr++;
			if (itr >= 5) {
				if (!afixflag)
					a[1] = atmp;
				if (!sfixflag)
					ptr[1] = stmp;
				//printf("Out of bound %d, under approximation a fixed point!\n", 5);
				break;
			}
		}
	}

	ptr[2] = dfaMinimize(
			dfaProduct(ptr[0], dfaASCIIOnlyNullString(svar, sindices), dfaAND));
	dfaPrintVerbose(ptr[2]);

	uL = dfa_string_to_unaryDFA(ptr[2], svar, sindices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);
	print_semilinear_coefficients(s);

	reset_coeffs(coeffs, var);
	coeffs[0] = 1;
	constant = 0;
	atmp = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	a[2] = dfaMinimize(dfaProduct(a[1], atmp, dfaAND));
	dfaPrintVerbose(a[2]);

	if (check_inclusion(a[2], assert, 2 * var, indices)) {
		if (afixflag)
			printf("Assertion Proven!\n");
		else
			printf("Assertion not violated within %d iteration", itr);
	} else {
		printf("Assertion Violated!\n");
	}

	printf("Memory Allocated: %d\n", mem_allocated());

	for (i = 0; i < 3; i++)
		dfaFree(a[i]);
	dfaFree(assert);

}

/***********************************************************************************************
 //This is the test prorgram for the following c codes
 // strrchr returns the substring from the last occurence of c in s
 //assertion(rlt \in c\Sigma* \cup {\epsilon})

 char* strrchr(char *s, char c){
 char *rlt = NULL;
 //r[0]
 while(*s ! = '\0'){
 if(*s=c)
 rlt = s;  //r[1]
 s++;
 //fixpoint: ptr = \Sigma^* \wedge ptr.length +cnt = s.length \wedge ptr.length >=0 (\{1+k|k>=0\})
 // r[2]
 }
 assert(*rlt \in c(\Sigma-c)*);
 //fixpoint: ptr = {} \wedge ptr.length +cnt = s.length \wedge ptr.length ==0
 //r[3]
 return rlt;
 }



 ********************************************************************************************************/

//var is equal to the number of string variables + the number of integer variables
void dfa_test_strrchr(int n) {

	DFA* rlt = NULL; //string automaton
	DFA* s = NULL; //an array of arithmetic automaton

	//string automaton
	int svar = NUM_ASCII_TRACKS;
	int* sindices = allocateAscIIIndexWithExtraBit(NUM_ASCII_TRACKS);
	DFA* stmp1 = NULL; //for fixed point computation
	DFA* stmpb = NULL; //for while branch condition
	DFA* stmpc = NULL; //for if branch condition
	DFA* tmp = NULL;
	int sfixflag = 0;
	DFA* assert = NULL;
	int itr = 0;

	rlt = dfaOnlyNullString(svar, sindices);

	//while(*s!='\0')
	stmpb = dfaASCIINotNullString(svar, sindices);
	stmpc = dfa_concat_extrabit(dfa_construct_string("c", svar, sindices),
			dfaAllStringASCIIExceptReserveWords(svar, sindices), svar,
			sindices);

	assert = dfaMinimize(dfaProduct(rlt, stmpc, dfaOR));
	//arbitrary input
	s = dfaAllStringASCIIExceptReserveWords(svar, sindices);

	while (itr < n) {
		printf("Iteration %d:\n", itr);
		stmp1 = dfaMinimize(dfaProduct(s, stmpb, dfaAND));
		stmp1 = dfaMinimize(dfaProduct(stmp1, stmpc, dfaAND));

		tmp = dfaMinimize(dfa_Prefix(stmp1, 1, 1, svar, sindices));
		if (check_inclusion(tmp, dfa_construct_string("c", svar, sindices),
				svar, sindices))
			printf("Prefix CORRECT!\n");
		else
			printf("Something Wrong with the Prefix\n.");
		dfaFree(tmp);

		stmp1 = dfaMinimize(dfaProduct(rlt, stmp1, dfaOR));
		dfaPrintVerbose(stmp1);
		stmp1 = dfaMinimize(dfaWiden(rlt, stmp1));
		if (check_inclusion(stmp1, rlt, svar, sindices)) {
			sfixflag = 1;
			printf("Reaching a fixed point!\n");
			break;
		} else {
			dfaFree(rlt);
			rlt = stmp1;
			s = dfaMinimize(dfa_Suffix(s, 1, 1, svar, sindices));
			itr++;
		}
	}

	if (check_inclusion(rlt, assert, svar, sindices)) {
		if (sfixflag)
			printf("Assertion Proven!\n");
		else
			printf("Assertion not violated within %d iterations.\n", itr);
	} else {
		printf("Assertion Violated!\n");
	}

	printf("Memory Allocated: %d\n", mem_allocated());
	dfaFree(s);
	dfaFree(stmpb);
	dfaFree(stmpc);
	dfaFree(rlt);
	dfaFree(stmp1);

}

/***********************************************************************************************
 //This is the test prorgram for the following c codes

 // simplified version of _nss_winbind_ipnodes_getbyname() in Samba

 static NSS_STATUS _nss_winbind_ipnodes_getbyname(char *name){
 char winsreq [FSTRING_LEN];
 r_strncpy(winsreq, name, strlen(name));
 return 0;
 }

 int main (){
 char in [INSZ];
 in [INSZ-1]=EOS;
 _nss_winbind_ipnodes_getbyname(in);
 return 0;
 }

 ********************************************************************************************************/

//var is equal to the number of string variables + the number of integer variables
void dfa_test_samba() {
	int var = 4; //0: in.length, 2: winsreq.length, 4:INSZ, 6:FSTRING_LEN
	DFA* in = NULL; //string automaton
	DFA* winsreq = NULL; //string automaton
	DFA* a; //an arithmetic automaton

	//arithmetic automaton
	int* indices;
	int* map;
	int* coeffs;
	int constant = 0;
	DFA* atmp = NULL;
	DFA* assert = NULL;

	//string automaton
	int svar = NUM_ASCII_TRACKS;
	int* sindices = allocateAscIIIndexWithExtraBit(NUM_ASCII_TRACKS);

	//semiliner
	DFA* uL = NULL;
	struct semilinear_type* s;

	indices = (int *) malloc(sizeof(int) * 2 * var);
	map = (int *) malloc(sizeof(int) * 2 * var);
	coeffs = (int *) malloc(sizeof(int) * 2 * var);

	dfa_init_indices_map_coeffs(indices, map, coeffs, var);

	//0: in.length, 2: winsreq.length, 4:INSZ, 6:FSTRING_LEN
	// [2] -[6] -1< 0
	reset_coeffs(coeffs, var);
	coeffs[2] = 1;
	coeffs[6] = -1;
	constant = -1;
	assert = build_DFA_ineq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	dfaPrintVerbose(assert);

	// char in [INSZ];
	// in[INSZ-1] = EOS;

	//string analysis
	in = dfaAllStringASCIIExceptReserveWords(svar, sindices); //\Sigma*

	//arithmetic analysis
	// [0]-[4]+1 =0
	reset_coeffs(coeffs, var);
	coeffs[0] = 1;
	coeffs[4] = -1;
	constant = 1;
	a = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	dfaPrintVerbose(a);

	//r_strncpy(winsreq, in, strlen(in));

	//string analysis
	winsreq = dfaCopy(in);

	//arithmetic analysis
	reset_coeffs(coeffs, var);
	coeffs[0] = -1;
	coeffs[2] = 1;
	constant = 0;
	atmp = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	a = dfaMinimize(dfaProduct(a, atmp, dfaAND));
	dfaFree(atmp);

	uL = dfa_string_to_unaryDFA(in, svar, sindices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);
	print_semilinear_coefficients(s);

	if (check_inclusion(a, assert, 2 * var, indices)) {
		printf("Assertion Proven!\n");
	} else {
		printf("Assertion Violated!\n");
	}

	printf("Memory Allocated: %d\n", mem_allocated());
	dfaFree(a);
	dfaFree(in);
	dfaFree(winsreq);
	dfaFree(assert);

}

/***********************************************************************************************
 //This is the test prorgram for the following c codes

 // simplified OK version of _nss_winbind_ipnodes_getbyname() in Samba

 static NSS_STATUS _nss_winbind_ipnodes_getbyname(char *name){
 char winsreq [FSTRING_LEN];
 r_strncpy(winsreq, name, FSTRING_LEN);
 return 0;
 }

 int main (){
 char in [INSZ];
 in [INSZ-1]=EOS;
 _nss_winbind_ipnodes_getbyname(in);
 return 0;
 }

 ********************************************************************************************************/

//var is equal to the number of string variables + the number of integer variables
void dfa_test_samba_ok() {
	int var = 4; //0: in.length, 2: winsreq.length, 4:INSZ, 6:FSTRING_LEN
	DFA* in = NULL; //string automaton
	DFA* winsreq = NULL; //string automaton
	DFA* a; //an arithmetic automaton

	//arithmetic automaton
	int* indices;
	int* map;
	int* coeffs;
	int constant = 0;
	DFA* atmp = NULL;
	DFA* assert = NULL;

	//string automaton
	int svar = NUM_ASCII_TRACKS;
	int* sindices = allocateAscIIIndexWithExtraBit(NUM_ASCII_TRACKS);

	//semiliner
	DFA* uL = NULL;
	struct semilinear_type* s;

	indices = (int *) malloc(sizeof(int) * 2 * var);
	map = (int *) malloc(sizeof(int) * 2 * var);
	coeffs = (int *) malloc(sizeof(int) * 2 * var);

	dfa_init_indices_map_coeffs(indices, map, coeffs, var);

	//0: in.length, 2: winsreq.length, 4:INSZ, 6:FSTRING_LEN
	// [2] -[6] -1< 0
	reset_coeffs(coeffs, var);
	coeffs[2] = 1;
	coeffs[6] = -1;
	constant = -1;
	assert = build_DFA_ineq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	dfaPrintVerbose(assert);

	// char in [INSZ];
	// in[INSZ-1] = EOS;

	//string analysis
	in = dfaAllStringASCIIExceptReserveWords(svar, sindices); //\Sigma*

	//arithmetic analysis
	// [0]-[4]+1 =0
	reset_coeffs(coeffs, var);
	coeffs[0] = 1;
	coeffs[4] = -1;
	constant = 1;
	a = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	dfaPrintVerbose(a);

	//r_strncpy(winsreq, in, FSTRING_LEN);

	//string analysis
	winsreq = dfaCopy(in);

	//arithmetic analysis
	reset_coeffs(coeffs, var);
	coeffs[0] = -1;
	coeffs[2] = 1;
	constant = 0;
	atmp = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	a = dfaMinimize(dfaProduct(a, atmp, dfaAND));
	dfaFree(atmp);

	//0: in.length, 2: winsreq.length, 4:INSZ, 6:FSTRING_LEN
	// [0] -[6] -1< 0
	reset_coeffs(coeffs, var);
	coeffs[0] = 1;
	coeffs[6] = -1;
	constant = -1;
	assert = build_DFA_ineq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	dfaPrintVerbose(assert);

	uL = dfa_string_to_unaryDFA(in, svar, sindices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);
	print_semilinear_coefficients(s);

	if (check_inclusion(a, assert, 2 * var, indices)) {
		printf("Assertion Proven!\n");
	} else {
		printf("Assertion Violated!\n");
	}

	printf("Memory Allocated: %d\n", mem_allocated());
	dfaFree(a);
	dfaFree(in);
	dfaFree(winsreq);
	dfaFree(assert);

}

//PHP programs (used in TACAS09)

/***********************************************************************************************
 /
 //This is the test prorgram for the following PHP codes

 <?php

 $www = $_GET["www"];
 $limit = (int)$_GET["limit"];
 $l_otherinfo = "URL";

 $www = ereg_replace("[^A-Za-z0-9 .\-@://]","",$www);
 if(strlen($www) < $limit) {
 echo "<td>" . $l_otherinfo . ": " . $www . "</td>";
 }

 ?>

 ********************************************************************************************************/

//[^A-Za-z0-9 .-@:/]
DFA *dfaSpecial2(int var, int *indices) {
	unsigned long n;
	char a = ' ';
	dfaSetup(3, var, indices);
	dfaAllocExceptions(74);
	dfaStoreException(1, bintostr((unsigned long) a, var));
	for (n = 46; n <= 90; n++)
		dfaStoreException(1, bintostr(n, var));
	for (n = 97; n <= 122; n++)
		dfaStoreException(1, bintostr(n, var));
	dfaStoreException(1, getSharp1(var));
	dfaStoreException(1, getSharp0(var));
	dfaStoreState(2);

	//state 1
	dfaAllocExceptions(0);
	dfaStoreState(1);

	//state 2
	dfaAllocExceptions(0);
	dfaStoreState(1);

	return dfaBuild("--+");
}

//[^A-Za-z0-9 .\-@:/]
DFA *dfaSpecial3(int var, int *indices) {
	unsigned long n;
	char a = ' ';
	dfaSetup(3, var, indices);
	dfaAllocExceptions(70);
	dfaStoreException(1, bintostr((unsigned long) a, var));

	for (n = 45; n <= 58; n++)
		dfaStoreException(1, bintostr(n, var));
	for (n = 64; n <= 90; n++)
		dfaStoreException(1, bintostr(n, var));
	for (n = 97; n <= 122; n++)
		dfaStoreException(1, bintostr(n, var));
	dfaStoreException(1, getSharp1(var));
	dfaStoreException(1, getSharp0(var));
	dfaStoreState(2);

	//state 1
	dfaAllocExceptions(0);
	dfaStoreState(1);

	//state 2
	dfaAllocExceptions(0);
	dfaStoreState(1);

	return dfaBuild("--+");
}

DFA* construct_limit(DFA* M, int svar, int* sindices) {
	int var = 2; //0: attack.length, 2: limit
	DFA* a; //an arithmetic automaton

	//arithmetic automaton
	int* indices;
	int* map;
	int* coeffs;
	int constant = 0;

	//semiliner

	indices = (int *) malloc(sizeof(int) * 2 * var);
	map = (int *) malloc(sizeof(int) * 2 * var);
	coeffs = (int *) malloc(sizeof(int) * 2 * var);

	dfa_init_indices_map_coeffs(indices, map, coeffs, var);

	//arithmetic analysis
	//0: www.length, 2: limit
	reset_coeffs(coeffs, var);
	coeffs[0] = 1;
	coeffs[2] = -1;
	constant = -1;
	a = build_DFA_ineq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	/*
	 uL = dfa_string_to_unaryDFA(M, svar, sindices);
	 s=getSemilinerSetCoefficients(uL);
	 printf("\n Unary Length Automaton:\n");
	 dfaPrintVerbose(uL);
	 print_semilinear_coefficients(s);
	 */
	return a;
}

void dfa_test_myez() {
	int var = 2; //0: attack.length, 2: limit
	DFA* a; //an arithmetic automaton

	int i;
	//arithmetic automaton
	int* indices;
	int* map;
	int* coeffs;
	int constant = 0;

	//string automaton
	int svar = NUM_ASCII_TRACKS;
	int* sindices = allocateAscIIIndexWithExtraBit(NUM_ASCII_TRACKS);
	DFA* attack = NULL; //for fixed point computation
	DFA* M[4];
	DFA* stmp;

	//semiliner
	DFA* uL = NULL;
	struct semilinear_type* s;

	indices = (int *) malloc(sizeof(int) * 2 * var);
	map = (int *) malloc(sizeof(int) * 2 * var);
	coeffs = (int *) malloc(sizeof(int) * 2 * var);

	dfa_init_indices_map_coeffs(indices, map, coeffs, var);

	//attack strings
	attack = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(svar, sindices),
			dfa_construct_string("<script ", svar, sindices), svar, sindices);
	attack = dfa_concat_extrabit(attack,
			dfaAllStringASCIIExceptReserveWords(svar, sindices), svar,
			sindices);

	//string analysis
	M[0] = dfaAllStringASCIIExceptReserveWords(svar, sindices); //$www
	//dfaPrintVerbose(M[0]);
	M[1] = dfa_construct_string("URL", svar, sindices);
	//dfaPrintVerbose(M[1]);
	M[2] = dfaSpecial2(svar, sindices); //for [^A-Za-z0-9 .-@:/]
	//dfaPrintVerbose(M[2]);
	M[3] = dfa_replace_extrabit(M[0], M[2], "", svar, sindices);

	dfaFree(M[0]);
	M[0] = dfa_construct_string("<td>", svar, sindices);
	M[0] = dfa_concat_extrabit(M[0], M[1], svar, sindices);
	M[0] = dfa_concat_extrabit(M[0], dfa_construct_string(": ", svar, sindices),
			svar, sindices);
	M[0] = dfa_concat_extrabit(M[0], M[3], svar, sindices);
	M[0] = dfa_concat_extrabit(M[0],
			dfa_construct_string("</td>", svar, sindices), svar, sindices);

	//dfaPrintVitals(M[0]);

	//arithmetic analysis
	//0: www.length, 2: limit
	reset_coeffs(coeffs, var);
	coeffs[0] = 1;
	coeffs[2] = -1;
	constant = -1;
	a = build_DFA_ineq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0

	//One should compute teh reange of $www.length from a
	//Here it is [0,inf].
	//Construct \Sigma^[0,inf]
	stmp = dfaAllStringASCIIExceptReserveWords(svar, sindices);
	M[0] = dfaMinimize(dfaProduct(M[0], stmp, dfaAND));

	i = check_intersection(M[0], attack, svar, sindices);
	if (i == 0)
		printf("Result: Secure!\n");
	else if (i == 1)
		printf("Result: Vulnerable!\n");
	else
		printf("Result: error in dfa_test_vul1_Saint() !\n");

	uL = dfa_string_to_unaryDFA(M[0], svar, sindices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);
	print_semilinear_coefficients(s);

	printf("Memory Allocated: %d\n", mem_allocated());
	for (i = 0; i < 4; i++)
		dfaFree(M[i]);
	dfaFree(attack);
	dfaFree(stmp);
	dfaFree(uL);
	dfaFree(a);
}

/***********************************************************************************************
 //This is the test prorgram for the following c codes

 // simplified version of gxine CVE-2007-0406

 int main (){
 struct sockaddr_un serv_adr;
 char filename[FILENAME_SZ];

 filename[FILENAME_SZ-1]=EOS;
 r_strcpy(serv_adr.sun_path, filename);
 return 0;
 }

 ********************************************************************************************************/

//var is equal to the number of string variables + the number of integer variables
void dfa_test_gxine() {
	int var = 4; //0: filename.length, 2: sunpath.length, 4:FILENAME_SZ, 6:SUNPATH_SZ
	DFA* filename = NULL; //string automaton
	DFA* sunpath = NULL; //string automaton
	DFA* a; //an arithmetic automaton

	//arithmetic automaton
	int* indices;
	int* map;
	int* coeffs;
	int constant = 0;
	DFA* atmp = NULL;
	DFA* assert = NULL;

	//string automaton
	int svar = NUM_ASCII_TRACKS;
	int* sindices = allocateAscIIIndexWithExtraBit(NUM_ASCII_TRACKS);

	//semiliner
	DFA* uL = NULL;
	struct semilinear_type* s;

	indices = (int *) malloc(sizeof(int) * 2 * var);
	map = (int *) malloc(sizeof(int) * 2 * var);
	coeffs = (int *) malloc(sizeof(int) * 2 * var);

	dfa_init_indices_map_coeffs(indices, map, coeffs, var);

	//0: filename.length, 2: sunpath.length, 4:FILENAME_SZ, 6:SUNPATH_SZ

	// [2] -[6] -1< 0
	reset_coeffs(coeffs, var);
	coeffs[2] = 1;
	coeffs[6] = -1;
	constant = -1;
	assert = build_DFA_ineq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	dfaPrintVerbose(assert);

	// char filename[FILENAME_SZ];
	//  filename[FILENAME_SZ-1]=EOS;

	//string analysis
	filename = dfaAllStringASCIIExceptReserveWords(svar, sindices); //\Sigma*

	//arithmetic analysis
	// [0]-[4]+1 =0
	reset_coeffs(coeffs, var);
	coeffs[0] = 1;
	coeffs[4] = -1;
	constant = 1;
	a = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	dfaPrintVerbose(a);

	//r_strcpy(serv_adr.sun_path, filename);

	//string analysis
	sunpath = dfaCopy(filename);

	//arithmetic analysis
	reset_coeffs(coeffs, var);
	coeffs[0] = -1;
	coeffs[2] = 1;
	constant = 0;
	atmp = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	a = dfaMinimize(dfaProduct(a, atmp, dfaAND));
	dfaFree(atmp);

	uL = dfa_string_to_unaryDFA(sunpath, svar, sindices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);
	print_semilinear_coefficients(s);

	if (check_inclusion(a, assert, 2 * var, indices)) {
		printf("Assertion Proven!\n");
	} else {
		printf("Assertion Violated!\n");
	}

	printf("Memory Allocated: %d\n", mem_allocated());
	dfaFree(a);
	dfaFree(filename);
	dfaFree(sunpath);
	dfaFree(assert);

}

/***********************************************************************************************
 //This is the test prorgram for the following c codes

 // simplified version of gxine OK CVE-2007-0406

 int main (){
 struct sockaddr_un serv_adr;
 char filename[FILENAME_SZ];

 filename[FILENAME_SZ-1]=EOS;
 r_strncpy(serv_adr.sun_path, filename, SUNPATH_SZ);
 return 0;
 }

 ********************************************************************************************************/

//var is equal to the number of string variables + the number of integer variables
void dfa_test_gxine_ok() {
	int var = 4; //0: filename.length, 2: sunpath.length, 4:FILENAME_SZ, 6:SUNPATH_SZ
	DFA* filename = NULL; //string automaton
	DFA* sunpath = NULL; //string automaton
	DFA* a; //an arithmetic automaton

	//arithmetic automaton
	int* indices;
	int* map;
	int* coeffs;
	int constant = 0;
	DFA* atmp = NULL;
	DFA* assert = NULL;

	//string automaton
	int svar = NUM_ASCII_TRACKS;
	int* sindices = allocateAscIIIndexWithExtraBit(NUM_ASCII_TRACKS);

	//semiliner
	DFA* uL = NULL;
	struct semilinear_type* s;

	indices = (int *) malloc(sizeof(int) * 2 * var);
	map = (int *) malloc(sizeof(int) * 2 * var);
	coeffs = (int *) malloc(sizeof(int) * 2 * var);

	dfa_init_indices_map_coeffs(indices, map, coeffs, var);

	//0: filename.length, 2: sunpath.length, 4:FILENAME_SZ, 6:SUNPATH_SZ

	// [2] -[6] -1< 0
	reset_coeffs(coeffs, var);
	coeffs[2] = 1;
	coeffs[6] = -1;
	constant = -1;
	assert = build_DFA_ineq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	dfaPrintVerbose(assert);

	// char filename[FILENAME_SZ];
	//  filename[FILENAME_SZ-1]=EOS;

	//string analysis
	filename = dfaAllStringASCIIExceptReserveWords(svar, sindices); //\Sigma*

	//arithmetic analysis
	// [0]-[4]+1 =0
	reset_coeffs(coeffs, var);
	coeffs[0] = 1;
	coeffs[4] = -1;
	constant = 1;
	a = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	dfaPrintVerbose(a);

	//r_strncpy(serv_adr.sun_path, filename);

	//string analysis
	sunpath = dfaCopy(filename);

	//arithmetic analysis
	reset_coeffs(coeffs, var);
	coeffs[0] = -1;
	coeffs[2] = 1;
	constant = 0;
	atmp = build_DFA_eq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	a = dfaMinimize(dfaProduct(a, atmp, dfaAND));
	dfaFree(atmp);

	//arithmetic analysis
	reset_coeffs(coeffs, var);
	coeffs[2] = 1;
	coeffs[6] = -1;
	constant = -1;
	atmp = build_DFA_ineq_2sc(2 * var, coeffs, constant, indices); //Constructs a DFA for the equation coeffs*variables+constant=0
	a = dfaMinimize(dfaProduct(a, atmp, dfaAND));
	dfaFree(atmp);

	uL = dfa_string_to_unaryDFA(sunpath, svar, sindices);
	s = getSemilinerSetCoefficients(uL);
	printf("\n Unary Length Automaton:\n");
	dfaPrintVerbose(uL);
	print_semilinear_coefficients(s);

	if (check_inclusion(a, assert, 2 * var, indices)) {
		printf("Assertion Proven!\n");
	} else {
		printf("Assertion Violated!\n");
	}

	printf("Memory Allocated: %d\n", mem_allocated());
	dfaFree(a);
	dfaFree(filename);
	dfaFree(sunpath);
	dfaFree(assert);

}

void dfa_test_replace(int var, int* indices) {
	printf("Running dfa_test_replace.\n");
	DFA* m[50];
//	1 = makeString(<SCRIPT)
	m[0] = dfa_construct_string("<SCRIPT", var, indices); //1
//	2 = makeDot()
	m[1] = dfaDot(var, indices); //2
//	3 = kleensStar(2) -- start
//	2 = closure(2)
//	3 = unionWithEmptyString(2) -- start
//	-100 = makeEmptyString()
//	3 = union(2, -100)
//	3 = unionWithEmptyString(2) -- end
//	3 = kleensStar(2) -- end
	m[2] = dfa_closure_extrabit(m[1], var, indices);
	m[3] = dfaASCIIOnlyNullString(var, indices);
	m[4] = dfa_union_with_emptycheck(m[2], m[3], var, indices); //3
//	4 = makeOptional(3) -- start
//	4 = unionWithEmptyString(3) -- start
//	-100 = makeEmptyString()
//	4 = union(3, -100)
//	4 = unionWithEmptyString(3) -- end
//	4 = makeOptional(3) -- end
	m[5] = dfaASCIIOnlyNullString(var, indices);
	m[6] = dfa_union_with_emptycheck(m[5], m[4], var, indices); //4
//	5 = makeChar(>) -- start
//	5 = makeString(>)
//	5 = makeChar(>) -- end
	m[7] = dfa_construct_string(">", var, indices); //5
//	6 = makeDot()
	m[8] = dfaDot(var, indices); //6
//	7 = kleensStar(6) -- start
//	6 = closure(6)
//	7 = unionWithEmptyString(6) -- start
//	-100 = makeEmptyString()
//	7 = union(6, -100)
//	7 = unionWithEmptyString(6) -- end
//	7 = kleensStar(6) -- end
	m[9] = dfa_closure_extrabit(m[8], var, indices);
	m[10] = dfaASCIIOnlyNullString(var, indices);
	m[11] = dfa_union_with_emptycheck(m[10], m[9], var, indices); //7
//	8 = makeOptional(7) -- start
//	8 = unionWithEmptyString(7) -- start
//	-100 = makeEmptyString()
//	8 = union(7, -100)
//	8 = unionWithEmptyString(7) -- end
//	8 = makeOptional(7) -- end
	m[12] = dfaASCIIOnlyNullString(var, indices);
	m[13] = dfa_union_with_emptycheck(m[12], m[11], var, indices); //8
//	9 = makeString(</SCRIPT)
	m[14] = dfa_construct_string("</SCRIPT", var, indices); //9
//	10 = makeDot()
	m[15] = dfaDot(var, indices); //10
//	11 = kleensStar(10) -- start
//	10 = closure(10)
//	11 = unionWithEmptyString(10) -- start
//	-100 = makeEmptyString()
//	11 = union(10, -100)
//	11 = unionWithEmptyString(10) -- end
//	11 = kleensStar(10) -- end
	m[16] = dfa_closure_extrabit(m[15], var, indices);
	m[17] = dfaASCIIOnlyNullString(var, indices);
	m[18] = dfa_union_with_emptycheck(m[17], m[17], var, indices); //11
//	12 = makeOptional(11) -- start
//	12 = unionWithEmptyString(11) -- start
//	-100 = makeEmptyString()
//	12 = union(11, -100)
//	12 = unionWithEmptyString(11) -- end
//	12 = makeOptional(11) -- end
	m[19] = dfaASCIIOnlyNullString(var, indices);
	m[20] = dfa_union_with_emptycheck(m[19], m[18], var, indices); //12
//	13 = makeChar(>) -- start
//	13 = makeString(>)
//	13 = makeChar(>) -- end
	m[21] = dfa_construct_string(">", var, indices); //13
//	14 = concatenate(12, 13)
	m[22] = dfa_concat_extrabit(m[20], m[21], var, indices); //14
//	15 = concatenate(9, 14)
	m[23] = dfa_concat_extrabit(m[14], m[22], var, indices); //15
//	16 = concatenate(8, 15)
	m[24] = dfa_concat_extrabit(m[13], m[23], var, indices); //16
//	17 = concatenate(5, 16)
	m[25] = dfa_concat_extrabit(m[7], m[24], var, indices); //17
//	18 = concatenate(4, 17)
	m[26] = dfa_concat_extrabit(m[6], m[25], var, indices); //18
//	19 = concatenate(1, 18)
	m[27] = dfa_concat_extrabit(m[0], m[26], var, indices); //19, 44

	char replace_string[] = "SCRIPT BLOCKED";
	m[28] = dfaAllStringASCIIExceptReserveWords(var, indices); //47
//	calling reg_replace with the following order (47, 44, SCRIPT BLOCKED)
	m[29] = dfa_replace_extrabit(m[29], m[27], replace_string, var, indices);
	int i = 0;
	for (i = 0; i < 30; i++)
		dfaFree(m[i]);
	printf("Finished dfa_test_replace.\n");
}

//PHP programs (used in TACAS09)

/***********************************************************************************************
 /
 //This is the test prorgram for the following PHP codes  (prod.php 176)

 <?php

 $userfile = $_GET["file"];
 $userfile = ereg_replace("[^A-Za-z0-9/ ,_-]","",$userfile);

 $password="";
 if($userfile==""){

 $possible_charactors = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
 while(strlen($password)<16) {
 $password .= substr($possible_charactors,(rand()%(strlen($possible_charactors))),1);
 }
 $password=$password.".jpg";
 $sql="select poza from shopprod where poza like '$password';";
 $result = mysql_query($sql, $link);
 }
 ?>
 ********************************************************************************************************/

/***********************************************************************************************
 Manual Testing Programs
 For real PHP programs (used in SPIN08)

 ********************************************************************************************************/

//[A-Za-z0-9]+
DFA *dfaSpecial1(int var, int *indices) {
	unsigned long n;
	dfaSetup(3, var, indices);
	dfaAllocExceptions(62);

	for (n = 48; n <= 57; n++)
		dfaStoreException(1, bintostr(n, var));
	for (n = 65; n <= 90; n++)
		dfaStoreException(1, bintostr(n, var));
	for (n = 97; n <= 122; n++)
		dfaStoreException(1, bintostr(n, var));
	dfaStoreState(2);

	//state 1
	dfaAllocExceptions(62);

	for (n = 48; n <= 57; n++)
		dfaStoreException(1, bintostr(n, var));
	for (n = 65; n <= 90; n++)
		dfaStoreException(1, bintostr(n, var));
	for (n = 97; n <= 122; n++)
		dfaStoreException(1, bintostr(n, var));
	dfaStoreState(2);

	//state 2
	dfaAllocExceptions(0);
	dfaStoreState(2);

	return dfaBuild("-+-");
}

void dfa_example(int var, int *indices) {
	int i;
	DFA *M[3];
	M[1] = dfa_construct_string("baab", var, indices);
	M[2] = dfa_construct_string_closure("a", var, indices);
	M[0] = dfa_replace_extrabit(M[1], M[2], "c", var, indices);
	printf("M1:baaab\n");
	dfaPrintVerbose(M[1]);
	//dfaPrintGraphviz(M[1], var, indices);
	printf("M2:[A-Za-z0-9]+\n");
	dfaPrintVerbose(M[2]);
	//dfaPrintGraphviz(M[2], var, indices);
	printf("M0=replace(M1, M2, emp)\n");
	dfaPrintVerbose(M[0]);
	//dfaPrintGraphviz(M[0], var, indices);
	for (i = 0; i < 3; i++)
		dfaFree(M[i]);
}

/***********************************************************************************************
 //This is the test prorgram for the following PHP codes
 // simplified version of the vulnerability:
 //     program: MyEasyMarket-4.1
 //     file: buy.php:138, trans.php:218



 <?php

 $www = $_GET["www"];
 $limit = (int)$_GET["limit"];
 $l_otherinfo = "URL";

 $www = ereg_replace("[^A-Za-z0-9 .-@://]","",$www);
 echo "<center><table border=1\>";

 for ($i = 0; $i < $limit; $i++) {
 echo "<td>" . $l_otherinfo . ": " . $www . "</td>";
 }
 echo "</table>";

 ?>

 ********************************************************************************************************/

void dfa_test_vul1(int var, int *indices) {
	int i = -1;
	DFA *M[4];
	DFA *tmpM;

	//attack strings
	tmpM = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<script ", var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	printf("\n\nSTART Test Vul1 !\n");
	M[0] = dfaAllStringASCIIExceptReserveWords(var, indices); //$www
	//dfaPrintVerbose(M[0]);
	M[1] = dfa_construct_string("URL", var, indices);
	//dfaPrintVerbose(M[1]);
	M[2] = dfaSpecial2(var, indices); //for [^A-Za-z0-9 .-@:/]
	//dfaPrintVerbose(M[2]);
	M[3] = dfa_replace_extrabit(M[0], M[2], "", var, indices);

	dfaFree(M[0]);
	M[0] = dfa_construct_string("<td>", var, indices);
	M[0] = dfa_concat_extrabit(M[0], M[1], var, indices);
	M[0] = dfa_concat_extrabit(M[0], dfa_construct_string(": ", var, indices),
			var, indices);
	M[0] = dfa_concat_extrabit(M[0], M[3], var, indices);
	M[0] = dfa_concat_extrabit(M[0],
			dfa_construct_string("</td>", var, indices), var, indices);

	//dfaPrintVitals(M[0]);

	//M[4] = dfa_construct_string("<script src=http://evil.com/attack.js>", var, indices);
	//dfaPrintVerbose(M[4]);

	i = check_intersection(M[0], tmpM, var, indices);
	if (i == 0)
		printf("Result: Secure!\n");
	else if (i == 1)
		printf("Result: Vulnerable!\n");
	else
		printf("Result: error in dfa_test_vul1() !\n");

	printf("Memory Allocated: %d\n", mem_allocated());
	for (i = 0; i < 4; i++)
		dfaFree(M[i]);
	dfaFree(tmpM);
}

/***********************************************************************************************
 //Vun01 Saint
 //This is the test prorgram for the following PHP codes

 <?php

 $www = $_GET["www"];
 $limit = (int)$_GET["limit"];
 $l_otherinfo = "URL";

 $www = ereg_replace("[^A-Za-z0-9 .\-@://]","",$www);
 echo "<center><table border=1\>";

 for ($i = 0; $i < $limit; $i++) {
 echo "<td>" . $l_otherinfo . ": " . $www . "</td>";
 }
 echo "</table>";

 ?>

 ********************************************************************************************************/

void dfa_test_vul1_saint(int var, int *indices) {
	int i = -1;
	DFA *M[4];
	DFA *tmpM;

	//attack strings
	tmpM = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<script ", var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	printf("\n\nSTART Test Vul1 Saint!\n");
	M[0] = dfaAllStringASCIIExceptReserveWords(var, indices); //$www
	//dfaPrintVerbose(M[0]);
	M[1] = dfa_construct_string("URL", var, indices);
	//dfaPrintVerbose(M[1]);
	M[2] = dfaSpecial3(var, indices); //for [^A-Za-z0-9 .-@:/]
	//dfaPrintVerbose(M[2]);
	M[3] = dfa_replace_extrabit(M[0], M[2], "", var, indices);

	dfaFree(M[0]);
	M[0] = dfa_construct_string("<td>", var, indices);
	M[0] = dfa_concat_extrabit(M[0], M[1], var, indices);
	M[0] = dfa_concat_extrabit(M[0], dfa_construct_string(": ", var, indices),
			var, indices);
	M[0] = dfa_concat_extrabit(M[0], M[3], var, indices);
	M[0] = dfa_concat_extrabit(M[0],
			dfa_construct_string("</td>", var, indices), var, indices);

	//dfaPrintVitals(M[0]);

	//M[4] = dfa_construct_string("<script src=http://evil.com/attack.js>", var, indices);
	//dfaPrintVerbose(M[4]);

	i = check_intersection(M[0], tmpM, var, indices);
	if (i == 0)
		printf("Result: Secure!\n");
	else if (i == 1)
		printf("Result: Vulnerable!\n");
	else
		printf("Result: error in dfa_test_vul1_Saint() !\n");

	printf("Memory Allocated: %d\n", mem_allocated());
	for (i = 0; i < 4; i++)
		dfaFree(M[i]);
	dfaFree(tmpM);
}

/***********************************************************************************************
 //Vunl02
 //This is the test prorgram for the following PHP codes
 // simplified version of the vulnerability:
 //   program: PBLguestbook-1.32
 //   file: pblguestbook.php:1210
 <?php

 function save_config() {
 foreach ($_POST as $name => $value) {
 if ($name != 'process' && $name != 'password2') {
 $count++;
 $result .= "`$name` = '$value'";
 if ($count <= $numofparts) {
 $result .= ", ";
 }
 }
 }
 $query = "UPDATE `pblguestbook_config` SET $result";

 return $query;
 }

 $result = save_config();
 mysql_query($result);

 ?>

 ********************************************************************************************************/

//`.\Sigma*.`='.\Sigma-{'}*.'
DFA *dfaSpecial4(int var, int *indices) {

	char a = '`';

	dfaSetup(7, var, indices);
	//state 0
	dfaAllocExceptions(1);
	dfaStoreException(1, bintostr((unsigned long) a, var));
	dfaStoreState(6); //sink states

	//state 1
	dfaAllocExceptions(3);
	dfaStoreException(2, bintostr((unsigned long) a, var));
	dfaStoreException(6, getSharp1(var));
	dfaStoreException(6, getSharp0(var));
	dfaStoreState(1);

	//state 2
	dfaAllocExceptions(1);
	a = '=';
	dfaStoreException(3, bintostr((unsigned long) a, var));
	dfaStoreState(6);

	//state 3
	dfaAllocExceptions(1);
	a = '\'';
	dfaStoreException(4, bintostr((unsigned long) a, var));
	dfaStoreState(6); //sink states

	//state 4
	dfaAllocExceptions(3);
	dfaStoreException(5, bintostr((unsigned long) a, var));
	dfaStoreException(6, getSharp1(var));
	dfaStoreException(6, getSharp0(var));
	dfaStoreState(4);

	//state 5
	dfaAllocExceptions(0);
	dfaStoreState(6); //sink states

	//state 6
	dfaAllocExceptions(0);
	dfaStoreState(6); //sink states

	return dfaMinimize(dfaBuild("-----+-"));
}

//`.\Sigma*.`='.\Sigma*
DFA *dfaSpecial4_1(int var, int *indices) {

	char a = '`';

	dfaSetup(6, var, indices);
	//state 0
	dfaAllocExceptions(1);
	dfaStoreException(1, bintostr((unsigned long) a, var));
	dfaStoreState(5); //sink states

	//state 1
	dfaAllocExceptions(3);
	dfaStoreException(2, bintostr((unsigned long) a, var));
	dfaStoreException(5, getSharp1(var));
	dfaStoreException(5, getSharp0(var));
	dfaStoreState(1);

	//state 2
	dfaAllocExceptions(1);
	a = '=';
	dfaStoreException(3, bintostr((unsigned long) a, var));
	dfaStoreState(5);

	//state 3
	dfaAllocExceptions(1);
	a = '\'';
	dfaStoreException(4, bintostr((unsigned long) a, var));
	dfaStoreState(5); //sink states

	//state 4
	dfaAllocExceptions(2);
	dfaStoreException(5, getSharp1(var));
	dfaStoreException(5, getSharp0(var));
	dfaStoreState(4);

	//state 5 (sink state)
	dfaAllocExceptions(0);
	dfaStoreState(5); //sink states

	return dfaMinimize(dfaBuild("----+-"));
}

//`.\Sigma*.`='.\Sigma*."', "
DFA *dfaSpecial5(int var, int *indices) {

	char a = '`';

	dfaSetup(9, var, indices);
	//state 0
	dfaAllocExceptions(1);
	dfaStoreException(1, bintostr((unsigned long) a, var));
	dfaStoreState(8); //sink states

	//state 1
	dfaAllocExceptions(3);
	dfaStoreException(2, bintostr((unsigned long) a, var));
	dfaStoreException(8, getSharp1(var));
	dfaStoreException(8, getSharp0(var));
	dfaStoreState(1);

	//state 2
	dfaAllocExceptions(1);
	a = '=';
	dfaStoreException(3, bintostr((unsigned long) a, var));
	dfaStoreState(8);

	//state 3
	dfaAllocExceptions(1);
	a = '\'';
	dfaStoreException(4, bintostr((unsigned long) a, var));
	dfaStoreState(8); //sink states

	//state 4
	dfaAllocExceptions(3);
	dfaStoreException(5, bintostr((unsigned long) a, var));
	dfaStoreException(8, getSharp1(var));
	dfaStoreException(8, getSharp0(var));
	dfaStoreState(4);

	//state 5
	dfaAllocExceptions(1);
	a = ',';
	dfaStoreException(6, bintostr((unsigned long) a, var));
	dfaStoreState(8); //sink states

	//state 6
	dfaAllocExceptions(1);
	a = ' ';
	dfaStoreException(7, bintostr((unsigned long) a, var));
	dfaStoreState(8); //sink states

	//state 7
	dfaAllocExceptions(0);
	dfaStoreState(8); //sink states

	//state 8
	dfaAllocExceptions(0);
	dfaStoreState(8); //sink states

	return dfaMinimize(dfaBuild("-------+-"));
}

DFA *dfaChar(char a, int var, int* indices) {
	dfaSetup(3, var, indices);
	//state 0
	dfaAllocExceptions(1);
	dfaStoreException(1, bintostr((unsigned long) a, var));
	dfaStoreState(2); //sink states

	//state 1
	dfaAllocExceptions(0);
	dfaStoreState(2); //sink states

	//state 2
	dfaAllocExceptions(0);
	dfaStoreState(2); //sink states

	return dfaMinimize(dfaBuild("0+-"));
}

//Vulnerable string
//`.\Sigma/{`}*.`='.\Sigma/{'}*."';".\Sigma*
DFA *dfaSpecial6(int var, int *indices) {

	char a = '`';

	dfaSetup(9, var, indices);
	//state 0
	dfaAllocExceptions(1);
	dfaStoreException(1, bintostr((unsigned long) a, var));
	dfaStoreState(8); //sink states

	//state 1
	dfaAllocExceptions(3);
	dfaStoreException(2, bintostr((unsigned long) a, var));
	dfaStoreException(8, getSharp1(var));
	dfaStoreException(8, getSharp0(var));
	dfaStoreState(1);

	//state 2
	dfaAllocExceptions(1);
	a = '=';
	dfaStoreException(3, bintostr((unsigned long) a, var));
	dfaStoreState(8);

	//state 3
	dfaAllocExceptions(1);
	a = '\'';
	dfaStoreException(4, bintostr((unsigned long) a, var));
	dfaStoreState(8); //sink states

	//state 4
	dfaAllocExceptions(3);
	dfaStoreException(5, bintostr((unsigned long) a, var));
	dfaStoreException(8, getSharp1(var));
	dfaStoreException(8, getSharp0(var));
	dfaStoreState(4);

	//state 5
	dfaAllocExceptions(1);
	a = ' ';
	dfaStoreException(6, bintostr((unsigned long) a, var));
	dfaStoreState(8); //sink states

	//state 6
	dfaAllocExceptions(2);
	dfaStoreException(6, bintostr((unsigned long) a, var));
	a = ';';
	dfaStoreException(7, bintostr((unsigned long) a, var));
	dfaStoreState(8); //sink states

	//state 7
	dfaAllocExceptions(2);
	dfaStoreException(8, getSharp1(var));
	dfaStoreException(8, getSharp0(var));
	dfaStoreState(7);

	//state 8
	dfaAllocExceptions(0);
	dfaStoreState(8); //sink states

	return dfaMinimize(dfaBuild("0000000+-"));
}

void dfa_test_vul2(int var, int *indices) {
#ifdef _COMPOSITE_ANALYSIS
	DFA* _a; //limit constraint
#endif
	int i = -1;
	int j = 0;
	DFA *M[11];
	//	DFA *tmpM;

	printf("\n\nSTART Test Vul2!\n");
	//	printf("Only Null String\n");
	M[0] = dfaASCIIOnlyNullString(var, indices); //$result
	//	dfaPrintVerbose(M[0]);
	//	printf("`.Sigma*.'='.Sigma*\n");
	M[9] = dfaSpecial4_1(var, indices); //`.\Sigma*.'='.\Sigma*
	M[10] = dfa_construct_string("'", var, indices);
	//	dfaPrintVerbose(M[9]);
	//	dfaPrintVerbose(M[10]);
	//	printf("Concat\n");
	M[1] = dfa_concat_extrabit(M[9], M[10], var, indices);
	//	dfaPrintVerbose(M[1]);
	//	printf("`.Sigma*.'='.Sigma*.', \n");
	dfaFree(M[10]);
	M[10] = dfa_construct_string("', ", var, indices);
	M[2] = dfa_concat_extrabit(M[9], M[10], var, indices); //`.\Sigma*.'='.\Sigma*."', "
	//	dfaPrintVerbose(M[2]);
	//	printf("Concat 1: .Sigma*.'='.Sigma*\n");
	//	M[3] = dfa_concat_extrabit(M[0], M[1], var, indices);
	//	dfaPrintVerbose(M[3]);
	//	printf("Concat 2: .Sigma*.'='.Sigma*`, \n");
	//	M[4] = dfa_concat_extrabit(M[0], M[2], var, indices);
	//	dfaPrintVerbose(M[4]);
	//	printf("Union Branch\n");
	M[5] = dfaMinimize(dfaProduct(M[1], M[2], dfaOR));
	//	dfaPrintVerbose(M[5]);
	//	printf("Union Iter 0 and Iter 1\n");
	M[6] = dfaMinimize(dfaProduct(M[0], M[5], dfaOR));

	dfaFree(M[0]);
	//	dfaFree(M[3]);
	//	dfaFree(M[4]);
	dfaFree(M[5]);

	while (i < 1 && j < 5) {
		j++;
		printf("Loop Iteration %d\n", j);
		M[0] = M[6]; //the ith step
		M[3] = dfa_concat_extrabit(M[0], M[1], var, indices);
		M[4] = dfa_concat_extrabit(M[0], M[2], var, indices);
		M[5] = dfaMinimize(dfaProduct(M[3], M[4], dfaOR));
		M[6] = dfaMinimize(dfaProduct(M[0], M[5], dfaOR)); //the i+1
		//dfaPrintVerbose(M[6]);
		i = check_inclusion(M[6], M[0], var, indices);
		//		printf("\n\nBefore Widening:\n", j);
		//		dfaPrintVerbose(M[6]);
		//		Use widening
		//		M[6]=dfaWiden(M[0], M[6]);
		//		printf("After Widening:\n", j);
		//		dfaPrintVerbose(M[6]);
		dfaFree(M[0]);
		dfaFree(M[3]);
		dfaFree(M[4]);
		dfaFree(M[5]);
	}

	dfaFree(M[1]);
	dfaFree(M[2]);

	//		printf("Widen:\n", j);
	//		dfaPrintVerbose(M[6]);

	M[7] = dfa_construct_string("UPDATE `pblguestbook_config` SET ", var,
			indices);
	M[8] = dfa_concat_extrabit(M[7], M[6], var, indices);
	//dfaPrintVerbose(M[8]);
	//Attack string
	M[1] = dfaSpecial6(var, indices);
	//	printf("Attack Strings\n");
	//	dfaPrintVerbose(M[1]);
	//	printf("Original Strings\n");
	//	dfaPrintVerbose(M[6]);
	M[2] = dfa_concat_extrabit(M[7], M[1], var, indices);

	//dfaPrintVitals(M[8]);

#ifdef _COMPOSITE_ANALYSIS
	_a = construct_limit(M[8], var, indices); //limit constraint
#endif

	i = check_intersection(M[8], M[2], var, indices);
	if (i == 0)
		printf("Result: Secure!\n");
	else if (i == 1)
		printf("Result: Vulnerable!\n");
	else
		printf("Result: error in dfa_test_vul1_saint() !\n");

	printf("Memory Allocated: %d\n", mem_allocated());

	for (j = 6; j < 11; j++)
		dfaFree(M[j]);
	dfaFree(M[1]);
	dfaFree(M[2]);

}

/***********************************************************************************************
 //Vun02 Saint

 <?php

 // simplified version of the vulnerability:
 //   program: PBLguestbook-1.32
 //   file: pblguestbook.php:1210


 function save_config() {
 foreach ($_POST as $name => $value) {
 if ($name != 'process' && $name != 'password2') {
 $count++;
 $value = replace("'", "", $value);
 $result .= "`$name` = '$value'";
 if ($count <= $numofparts) {
 $result .= ", ";
 }
 }
 }
 $query = "UPDATE `pblguestbook_config` SET $result";

 return $query;
 }

 $result = save_config();
 mysql_query($result);

 ?>


 ********************************************************************************************************/

//void dfa_test_vul2_saint(int var, int *indices) {
//
//#ifdef _COMPOSITE_ANALYSIS
//	DFA* _a; //limit constraint
//#endif
//	int i = -1;
//	int j = 0;
//	DFA *M[9];
//	//	DFA *tmpM;
//	printf("\n\nSTART Test Vul2 Saint !\n");
//	//	printf("\n\nSTART Test Vul2Saint!\n");
//	//	printf("Only Null String\n");
//	M[0] = dfaASCIIOnlyNullString(var, indices); //$result
//	//	dfaPrintVerbose(M[0]);
//	//	printf("`.Sigma*.'='.Sigma*.'\n");
//	M[1] = dfaSpecial4(var, indices); //`.\Sigma*.'='.\Sigma*.'
//	//	dfaPrintVerbose(M[1]);
//	//	printf("`.Sigma*.'='.Sigma*.', \n");
//	M[2] = dfaSpecial5(var, indices); //`.\Sigma*.'='.\Sigma*."', "
//	//	dfaPrintVerbose(M[2]);
//	//	printf("`Concat 1: .Sigma*.'='.Sigma*\n");
//	M[3] = dfa_concat_extrabit(M[0], M[1], var, indices);
//	//	dfaPrintVerbose(M[3]);
//	//	printf("`Concat 2: .Sigma*.'='.Sigma*`, \n");
//	M[4] = dfa_concat_extrabit(M[0], M[2], var, indices);
//	//	dfaPrintVerbose(M[4]);
//	//	printf("Union Branch\n");
//	M[5] = dfaMinimize(dfaProduct(M[3], M[4], dfaOR));
//	//	dfaPrintVerbose(M[5]);
//	//	printf("Union Iter 0 and Iter 1\n");
//	M[6] = dfaMinimize(dfaProduct(M[0], M[5], dfaOR));
//
//	dfaFree(M[0]);
//	dfaFree(M[3]);
//	dfaFree(M[4]);
//	dfaFree(M[5]);
//
//	while (i < 1 && j < 20) {
//		j++;
//		printf("Loop Iteration %d\n", j);
//		M[0] = M[6]; //the ith step
//		M[3] = dfa_concat_extrabit(M[0], M[1], var, indices);
//		M[4] = dfa_concat_extrabit(M[0], M[2], var, indices);
//		M[5] = dfaMinimize(dfaProduct(M[3], M[4], dfaOR));
//		M[6] = dfaMinimize(dfaProduct(M[0], M[5], dfaOR)); //the i+1
//		//		printf("\n\nBefore Widening:\n", j);
//				dfaPrintVerbose(M[6]);
//		i = check_inclusion(M[6], M[0], var, indices);
//		//		Use widening
//		M[6] = dfaWiden(M[0], M[6]);
//		printf("Widen: %d\n", j);// changed by muath : adding %d
//		dfaPrintVerbose(M[6]);
//
//		dfaFree(M[0]);
//		dfaFree(M[3]);
//		dfaFree(M[4]);
//		dfaFree(M[5]);
//	}
//
//	dfaFree(M[1]);
//	dfaFree(M[2]);
//
//	M[7] = dfa_construct_string("UPDATE `pblguestbook_config` SET ", var,
//			indices);
//	M[8] = dfa_concat_extrabit(M[7], M[6], var, indices);
//	//dfaPrintVerbose(M[8]);
//	//Attack string
//	M[1] = dfaSpecial6(var, indices);
//	M[2] = dfa_concat_extrabit(M[7], M[1], var, indices);
//
//	//dfaPrintVitals(M[8]);
//	i = check_intersection(M[8], M[2], var, indices);
//	if (i == 0)
//		printf("Result: Secure!\n");
//	else if (i == 1)
//		printf("Result: Vulnerable!\n");
//	else
//		printf("Result: error in dfa_test_vul1_saint() !\n");
//
//#ifdef _COMPOSITE_ANALYSIS
//	_a = construct_limit(M[8], var, indices); //limit constraint
//#endif
//
//	printf("Memory Allocated: %d\n", mem_allocated());
//
//	for (j = 6; j < 9; j++)
//		dfaFree(M[j]);
//	dfaFree(M[1]);
//	dfaFree(M[2]);
//}
void dfa_test_vul2_saint(int var, int *indices) {

#ifdef _COMPOSITE_ANALYSIS
	DFA* _a; //limit constraint
#endif
	int i = -1;
	int j = 0;
	DFA *M[9];
	//	DFA *tmpM;
	printf("\n\nSTART Test Vul2 Saint !\n");
	//	printf("\n\nSTART Test Vul2Saint!\n");
	//	printf("Only Null String\n");
	M[0] = dfaASCIIOnlyNullString(var, indices); //$result
	//	dfaPrintVerbose(M[0]);
	//	printf("`.Sigma*.'='.Sigma*.'\n");
	M[1] = dfaSpecial4(var, indices); //`.\Sigma*.'='.\Sigma*.'
	//	dfaPrintVerbose(M[1]);
	//	printf("`.Sigma*.'='.Sigma*.', \n");
	M[2] = dfaSpecial5(var, indices); //`.\Sigma*.'='.\Sigma*."', "
	//	dfaPrintVerbose(M[2]);
	//	printf("`Concat 1: .Sigma*.'='.Sigma*\n");
	M[3] = dfa_concat_extrabit(M[0], M[1], var, indices);
	//	dfaPrintVerbose(M[3]);
	//	printf("`Concat 2: .Sigma*.'='.Sigma*`, \n");
	M[4] = dfa_concat_extrabit(M[0], M[2], var, indices);
	//	dfaPrintVerbose(M[4]);
	//	printf("Union Branch\n");
	M[5] = dfaMinimize(dfaProduct(M[3], M[4], dfaOR));
	//	dfaPrintVerbose(M[5]);
	//	printf("Union Iter 0 and Iter 1\n");
	M[6] = dfaMinimize(dfaProduct(M[0], M[5], dfaOR));

	dfaFree(M[0]);
	dfaFree(M[3]);
	dfaFree(M[4]);
	dfaFree(M[5]);

	while (i < 1 && j < 20) {
		j++;
		printf("Loop Iteration %d\n", j);
		M[0] = M[6]; //the ith step
		M[3] = dfa_concat_extrabit(M[0], M[1], var, indices);
		M[4] = dfa_concat_extrabit(M[0], M[2], var, indices);
		M[5] = dfaMinimize(dfaProduct(M[3], M[4], dfaOR));
		M[6] = dfaMinimize(dfaProduct(M[0], M[5], dfaOR)); //the i+1
//    printf("\n\nBefore Widening:%d\n", j);
//    dfaPrintVerbose(M[0]);
//    dfaPrintVerbose(M[6]);

		i = check_inclusion(M[6], M[0], var, indices);
		//		Use widening
//    M[6]=dfaWiden(M[0], M[6]);
//    printf("\n\nAfter Widening:%d\n", j);
//    dfaPrintVerbose(M[6]);
		dfaFree(M[0]);
		dfaFree(M[3]);
		dfaFree(M[4]);
		dfaFree(M[5]);
	}

	dfaFree(M[1]);
	dfaFree(M[2]);

	M[7] = dfa_construct_string("UPDATE `pblguestbook_config` SET ", var,
			indices);
	M[8] = dfa_concat_extrabit(M[7], M[6], var, indices);
	//dfaPrintVerbose(M[8]);
	//Attack string
	M[1] = dfaSpecial6(var, indices);
	M[2] = dfa_concat_extrabit(M[7], M[1], var, indices);

	dfaPrintVitals(M[6]);
	i = check_intersection(M[8], M[2], var, indices);
	if (i == 0)
		printf("Result: Secure!\n");
	else if (i == 1)
		printf("Result: Vulnerable!\n");
	else
		printf("Result: error in dfa_test_vul1_saint() !\n");

#ifdef _COMPOSITE_ANALYSIS
	_a = construct_limit(M[8], var, indices); //limit constraint
#endif

	printf("Memory Allocated: %d\n", mem_allocated());

	for (j = 6; j < 9; j++)
		dfaFree(M[j]);
	dfaFree(M[1]);
	dfaFree(M[2]);
}

/***********************************************************************************************
 //Vuln03
 //This is the test prorgram for the following PHP codes

 <?php

 $config["link"] = "blue";
 $config["delbut"] = "http://localhost/delbut.png";
 $config["showip"] = "1";
 $config["ipbut"] = "http://localhost/ipbut.png";
 $thisprogram = "pblguestbook.php";
 $mes["email"] = "email address";


 if ($_SERVER['REMOTE_ADDR'] != '' && $config['showip'] == '1') {
 $ipbut = "&nbsp;<IMG SRC=$config[ipbut] BORDER=0 ALT=\"";
 $ipbut .= $_SERVER["REMOTE_ADDR"] . "\">&nbsp;";
 }

 $delbut = "&nbsp;<A STYLE=COLOR:$config[link]; HREF=$thisprogram?action=delete&id=$_POST[id]><IMG SRC=$config[delbut] BORDER=0 ALT=\"";


 if ($_POST['email'] != '') {
 $_POST["email"] = preg_replace("/\<SCRIPT(.*?)\>(.*?)\<\/SCRIPT(.*?)\>/i", "SCRIPT BLOCKED", $_POST["email"]);
 $emailbut = "&nbsp;<A STYLE=COLOR:$config[link]; HREF=\"mailto:$_POST[email]\"><IMG SRC=$config[emailbut] BORDER=0 ALT=\"";
 $emailbut .= $mes['email'] . "\"></A>&nbsp;";
 $pdata .= "</TD><TD STYLE=TEXT-ALIGN:right;><FONT SIZE=1>$emailbut$homebut$ipbut$delbut</FONT></TD></TR>";
 }

 echo $pdata;

 ?>


 ********************************************************************************************************/

void dfa_test_vul3(int var, int *indices) {

#ifdef _COMPOSITE_ANALYSIS
	DFA* _a; //limit constraint
#endif

	int i = -1;
	int j = 0;
	DFA *M[14];
	DFA *tmpM;
	/*
	 Var	"$config[delbut]"	0
	 Var	"$config[emailbut]"	1
	 Var	"$config[ipbut]"	2
	 Var	"$config[link]"		3
	 Var	"$config[showip]"	4
	 Var	"$delbut"		5
	 Var	"$emailbut"		6
	 //Var	"$homebut"		7
	 Var	"$ipbut"		8
	 Var	"$mes[email]"		9
	 Var	"$pdata"		10
	 Var	"$_POST[email]"		11
	 Var	"_t0_0"			12
	 Var	"$thisprogram"		13
	 Var	$_SERVER["REMOTE_ADDR"] 7
	 */

	printf("\n\nSTART Test Vul3!\n");
	//attack strings
	tmpM = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<script ", var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM, dfa_construct_string(">", var, indices),
			var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	M[3] = dfa_construct_string("blue", var, indices);
	M[0] = dfa_construct_string("http://localhost/delbut.png", var, indices);
	M[4] = dfa_construct_string("1", var, indices);
	M[2] = dfa_construct_string("http://localhost/ipbut.png", var, indices);
	M[13] = dfa_construct_string("pblguestbook.php", var, indices);
	M[9] = dfa_construct_string("email address", var, indices);
	M[1] = dfa_construct_string("configure emailbut", var, indices);
	M[7] = dfa_construct_string("127.0.0.1", var, indices); //this shall be fixed as x.x.x.x where x is [0-255]
	M[11] = dfaAllStringASCIIExceptReserveWords(var, indices); //.*

	M[12] = dfa_construct_string("&nbsp;<IMG SRC=", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[2], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string(" BORDER=0 ALT=\"", var, indices), var,
			indices);
	M[12] = dfa_concat_extrabit(M[12], M[7], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("\">&nbsp;", var, indices), var, indices);
	M[8] = M[12];
	//	dfaPrintVerbose(M[8]);

	M[12] = dfa_construct_string("&nbsp;<A STYLE=COLOR:", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[3], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("; HREF=", var, indices), var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[13], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("?action=delete&id=", var, indices), var,
			indices);
	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("><IMG SRC=", var, indices), var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[0], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string(" BORDER=0 ALT=\"", var, indices), var,
			indices);
	M[5] = M[12];

	M[12] = dfa_construct_string("<script", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	M[12] = dfa_concat_extrabit(M[12], dfa_construct_string(">", var, indices),
			var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("</script", var, indices), var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	M[12] = dfa_concat_extrabit(M[12], dfa_construct_string(">", var, indices),
			var, indices);
	M[11] = dfa_replace_extrabit(M[11], M[12], "SCRIPT BLOCKED", var, indices);

	M[12] = dfa_construct_string("&nbsp;<A STYLE=COLOR:", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[3], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("; HREF=\"mailto:", var, indices), var,
			indices);
	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("\"><IMG SRC=", var, indices), var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[1], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string(" BORDER=0 ALT=\"", var, indices), var,
			indices);
	M[6] = M[12];
	M[6] = dfa_concat_extrabit(M[6], M[9], var, indices);
	M[6] = dfa_concat_extrabit(M[6],
			dfa_construct_string("\"></A>&nbsp;", var, indices), var, indices);

	M[12] = dfa_construct_string(
			"</TD><TD STYLE=TEXT-ALIGN:right;><FONT SIZE=1>", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[6], var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[8], var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[5], var, indices);

	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("</FONT></TD></TR>", var, indices), var,
			indices);
	M[10] = M[12];
	M[12] = tmpM;

	//dfaPrintVitals(M[10]);

#ifdef _COMPOSITE_ANALYSIS
	_a = construct_limit(M[10], var, indices); //limit constraint
#endif
	printf("Memory Allocated: %d\n", mem_allocated());

	i = check_intersection(M[10], tmpM, var, indices);
	if (i == 0)
		printf("Result: Secure!\n");
	else if (i == 1)
		printf("Result: Vulnerable!\n");
	else
		printf("Result: error in dfa_test_vul1() !\n");

	for (j = 0; j < 14; j++) {
		//printf("Delete DFA %d\n", j);
		dfaFree(M[j]);
	}
}

/***********************************************************************************************
 //Vul03 Saint Fail
 //This is the test prorgram for the following PHP codes

 <?php

 $config["link"] = "blue";
 $config["delbut"] = "http://localhost/delbut.png";
 $config["showip"] = "1";
 $config["ipbut"] = "http://localhost/ipbut.png";
 $thisprogram = "pblguestbook.php";
 $mes["email"] = "email address";


 if ($_SERVER['REMOTE_ADDR'] != '' && $config['showip'] == '1') {
 $ipbut = "&nbsp;<IMG SRC=$config[ipbut] BORDER=0 ALT=\"";
 $ipbut .= $_SERVER["REMOTE_ADDR"] . "\">&nbsp;";
 }

 $delbut = "&nbsp;<A STYLE=COLOR:$config[link]; HREF=$thisprogram?action=delete&id=$_POST[id]><IMG SRC=$config[delbut] BORDER=0 ALT=\"";


 if ($_POST['email'] != '') {
 $_POST["email"] = preg_replace("/\<SCRIPT(.*?)\>/i", "SCRIPT BLOCKED", $_POST["email"]);
 $emailbut = "&nbsp;<A STYLE=COLOR:$config[link]; HREF=\"mailto:$_POST[email]\"><IMG SRC=$config[emailbut] BORDER=0 ALT=\"";
 $emailbut .= $mes['email'] . "\"></A>&nbsp;";
 $pdata .= "</TD><TD STYLE=TEXT-ALIGN:right;><FONT SIZE=1>$emailbut$homebut$ipbut$delbut</FONT></TD></TR>";
 }

 echo $pdata;

 ?>


 ********************************************************************************************************/

void dfa_test_vul3_saint_fail(int var, int *indices) {

#ifdef _COMPOSITE_ANALYSIS
	DFA* _a; //limit constraint
#endif

	int i = -1;
	int j = 0;
	DFA *M[14];
	DFA *tmpM;
	/*
	 Var	"$config[delbut]"	0
	 Var	"$config[emailbut]"	1
	 Var	"$config[ipbut]"	2
	 Var	"$config[link]"		3
	 Var	"$config[showip]"	4
	 Var	"$delbut"		5
	 Var	"$emailbut"		6
	 //Var	"$homebut"		7
	 Var	"$ipbut"		8
	 Var	"$mes[email]"		9
	 Var	"$pdata"		10
	 Var	"$_POST[email] and _POST[id]"		11
	 Var	"_t0_0"			12
	 Var	"$thisprogram"		13
	 Var	$_SERVER["REMOTE_ADDR"] 7
	 */

	printf("\n\nSTART Test Vul3 Saint Fail!\n");
	//attack strings
	tmpM = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<script ", var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM, dfa_construct_string(">", var, indices),
			var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	M[3] = dfa_construct_string("blue", var, indices);
	M[0] = dfa_construct_string("http://localhost/delbut.png", var, indices);
	M[4] = dfa_construct_string("1", var, indices);
	M[2] = dfa_construct_string("http://localhost/ipbut.png", var, indices);
	M[13] = dfa_construct_string("pblguestbook.php", var, indices);
	M[9] = dfa_construct_string("email address", var, indices);
	M[1] = dfa_construct_string("configure emailbut", var, indices);
	M[7] = dfa_construct_string("127.0.0.1", var, indices); //this shall be fixed as x.x.x.x where x is [0-255]
	M[11] = dfaAllStringASCIIExceptReserveWords(var, indices); //.*

	M[12] = dfa_construct_string("&nbsp;<IMG SRC=", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[2], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string(" BORDER=0 ALT=\"", var, indices), var,
			indices);
	M[12] = dfa_concat_extrabit(M[12], M[7], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("\">&nbsp;", var, indices), var, indices);
	M[8] = M[12];
	//	dfaPrintVerbose(M[8]);

	M[12] = dfa_construct_string("&nbsp;<A STYLE=COLOR:", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[3], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("; HREF=", var, indices), var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[13], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("?action=delete&id=", var, indices), var,
			indices);
	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("><IMG SRC=", var, indices), var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[0], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string(" BORDER=0 ALT=\"", var, indices), var,
			indices);
	M[5] = M[12];

	M[12] = dfa_construct_string("<script", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	M[12] = dfa_concat_extrabit(M[12], dfa_construct_string(">", var, indices),
			var, indices);
	//	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	//	M[12] = dfa_concat_extrabit(M[12], dfa_construct_string("</script ", var, indices), var, indices);
	//	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	//	M[12] = dfa_concat_extrabit(M[12], dfa_construct_string(">", var, indices), var, indices);
	M[11] = dfa_replace_extrabit(M[11], M[12], "SCRIPT BLOCKED", var, indices);

	M[12] = dfa_construct_string("&nbsp;<A STYLE=COLOR:", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[3], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("; HREF=\"mailto:", var, indices), var,
			indices);
	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("\"><IMG SRC=", var, indices), var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[1], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string(" BORDER=0 ALT=\"", var, indices), var,
			indices);
	M[6] = M[12];
	M[6] = dfa_concat_extrabit(M[6], M[9], var, indices);
	M[6] = dfa_concat_extrabit(M[6],
			dfa_construct_string("\"></A>&nbsp;", var, indices), var, indices);

	M[12] = dfa_construct_string(
			"</TD><TD STYLE=TEXT-ALIGN:right;><FONT SIZE=1>", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[6], var, indices);

	M[12] = dfa_concat_extrabit(M[12], M[8], var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[5], var, indices);
	i = check_intersection(M[5], tmpM, var, indices);

	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("</FONT></TD></TR>", var, indices), var,
			indices);
	M[10] = M[12];
	M[12] = tmpM;

	//dfaPrintVitals(M[10]);

#ifdef _COMPOSITE_ANALYSIS
	_a = construct_limit(M[10], var, indices); //limit constraint
#endif

	printf("Memory Allocated: %d\n", mem_allocated());

	i = check_intersection(M[10], tmpM, var, indices);
	if (i == 0)
		printf("Result: Secure!\n");
	else if (i == 1)
		printf("Result: Vulnerable!\n");
	else
		printf("Result: error in dfa_test_vul3() !\n");

	for (j = 0; j < 14; j++) {
		//printf("Delete DFA %d\n", j);
		dfaFree(M[j]);
	}
}

/***********************************************************************************************
 //Vuln03 Saint
 //This is the test prorgram for the following PHP codes

 <?php

 $config["link"] = "blue";
 $config["delbut"] = "http://localhost/delbut.png";
 $config["showip"] = "1";
 $config["ipbut"] = "http://localhost/ipbut.png";
 $thisprogram = "pblguestbook.php";
 $mes["email"] = "email address";


 if ($_SERVER['REMOTE_ADDR'] != '' && $config['showip'] == '1') {
 $ipbut = "&nbsp;<IMG SRC=$config[ipbut] BORDER=0 ALT=\"";
 $ipbut .= $_SERVER["REMOTE_ADDR"] . "\">&nbsp;";
 }
 $_POST[id] = preg_replace("/\<SCRIPT(.*?)\>/i", "SCRIPT BLOCKED", $_POST[id]);
 $delbut = "&nbsp;<A STYLE=COLOR:$config[link]; HREF=$thisprogram?action=delete&id=$_POST[id]><IMG SRC=$config[delbut] BORDER=0 ALT=\"";


 if ($_POST[email] != '') {
 $_POST[email] = preg_replace("/\<SCRIPT(.*?)\>/i", "SCRIPT BLOCKED", $_POST[email]);
 $emailbut = "&nbsp;<A STYLE=COLOR:$config[link]; HREF=\"mailto:$_POST[email]\"><IMG SRC=$config[emailbut] BORDER=0 ALT=\"";
 $emailbut .= $mes['email'] . "\"></A>&nbsp;";
 $pdata .= "</TD><TD STYLE=TEXT-ALIGN:right;><FONT SIZE=1>$emailbut$homebut$ipbut$delbut</FONT></TD></TR>";
 }

 echo $pdata;

 ?>


 ********************************************************************************************************/

void dfa_test_vul3_saint(int var, int *indices) {

#ifdef _COMPOSITE_ANALYSIS
	DFA* _a; //limit constraint
#endif

	int i = -1;
	int j = 0;
	DFA *M[14];
	DFA *tmpM;
	/*
	 Var	"$config[delbut]"	0
	 Var	"$config[emailbut]"	1
	 Var	"$config[ipbut]"	2
	 Var	"$config[link]"		3
	 Var	"$config[showip]"	4
	 Var	"$delbut"		5
	 Var	"$emailbut"		6
	 //Var	"$homebut"		7
	 Var	"$ipbut"		8
	 Var	"$mes[email]"		9
	 Var	"$pdata"		10
	 Var	"$_POST[email] and _POST[id]"		11
	 Var	"_t0_0"			12
	 Var	"$thisprogram"		13
	 Var	$_SERVER["REMOTE_ADDR"] 7
	 */

	printf("\n\nSTART Test Vul3 Saint !\n");
	//attack strings
	tmpM = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<script ", var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM, dfa_construct_string(">", var, indices),
			var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	M[3] = dfa_construct_string("blue", var, indices);
	M[0] = dfa_construct_string("http://localhost/delbut.png", var, indices);
	M[4] = dfa_construct_string("1", var, indices);
	M[2] = dfa_construct_string("http://localhost/ipbut.png", var, indices);
	M[13] = dfa_construct_string("pblguestbook.php", var, indices);
	M[9] = dfa_construct_string("email address", var, indices);
	M[1] = dfa_construct_string("configure emailbut", var, indices);
	M[7] = dfa_construct_string("127.0.0.1", var, indices); //this shall be fixed as x.x.x.x where x is [0-255]
	M[11] = dfaAllStringASCIIExceptReserveWords(var, indices); //.*

	M[12] = dfa_construct_string("&nbsp;<IMG SRC=", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[2], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string(" BORDER=0 ALT=\"", var, indices), var,
			indices);
	M[12] = dfa_concat_extrabit(M[12], M[7], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("\">&nbsp;", var, indices), var, indices);
	M[8] = M[12];
	//	dfaPrintVerbose(M[8]);

	M[12] = dfa_construct_string("<script", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	//	M[12] = dfa_concat_extrabit(M[12], dfa_construct_string(">", var, indices), var, indices);
	//	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	//	M[12] = dfa_concat_extrabit(M[12], dfa_construct_string("</script ", var, indices), var, indices);
	//	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	//	M[12] = dfa_concat_extrabit(M[12], dfa_construct_string(">", var, indices), var, indices);
	M[11] = dfa_replace_extrabit(M[11], M[12], "SCRIPT BLOCKED", var, indices);

	M[12] = dfa_construct_string("&nbsp;<A STYLE=COLOR:", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[3], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("; HREF=", var, indices), var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[13], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("?action=delete&id=", var, indices), var,
			indices);
	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("><IMG SRC=", var, indices), var, indices); //this may raise an attacking string "<script ><"
	M[12] = dfa_concat_extrabit(M[12], M[0], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string(" BORDER=0 ALT=\"", var, indices), var,
			indices);
	M[5] = M[12];

	M[12] = dfa_construct_string("&nbsp;<A STYLE=COLOR:", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[3], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("; HREF=\"mailto:", var, indices), var,
			indices);
	M[12] = dfa_concat_extrabit(M[12], M[11], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("\"><IMG SRC=", var, indices), var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[1], var, indices);
	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string(" BORDER=0 ALT=\"", var, indices), var,
			indices);
	M[6] = M[12];
	M[6] = dfa_concat_extrabit(M[6], M[9], var, indices);
	M[6] = dfa_concat_extrabit(M[6],
			dfa_construct_string("\"></A>&nbsp;", var, indices), var, indices);

	M[12] = dfa_construct_string(
			"</TD><TD STYLE=TEXT-ALIGN:right;><FONT SIZE=1>", var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[6], var, indices);

	M[12] = dfa_concat_extrabit(M[12], M[8], var, indices);
	M[12] = dfa_concat_extrabit(M[12], M[5], var, indices);
	i = check_intersection(M[5], tmpM, var, indices);

	M[12] = dfa_concat_extrabit(M[12],
			dfa_construct_string("</FONT></TD></TR>", var, indices), var,
			indices);
	M[10] = M[12];
	M[12] = tmpM;

	//dfaPrintVitals(M[10]);

#ifdef _COMPOSITE_ANALYSIS
	_a = construct_limit(M[10], var, indices); //limit constraint
#endif

	printf("Memory Allocated: %d\n", mem_allocated());

	i = check_intersection(M[10], tmpM, var, indices);
	if (i == 0)
		printf("Result: Secure!\n");
	else if (i == 1)
		printf("Result: Vulnerable!\n");
	else
		printf("Result: error in dfa_test_vul3() !\n");

	for (j = 0; j < 14; j++) {
		//printf("Delete DFA %d\n", j);
		dfaFree(M[j]);
	}

}

/***********************************************************************************************
 //Vuln04
 //This is the test prorgram for the following PHP codes

 <?php

 // Simplified version of the vulnerability:
 //   program: aphpkb-0.71
 //    file: global.php, saa.php:18, saa.php:87


 function escdata ($data) {
 $data = replace("'", "", $data);
 $data = replace('"', "", $data);
 $data = replace("\\\\", "\\", $data);
 return $data;
 }

 function xss_clean ($var) {
 $var = ereg_replace( '[Jj][Aa][Vv][Aa][Ss][Cc][Rr][Ii][Pp][Tt]', 'java script', $var );
 return $var;
 }

 $titlee = escdata(xss_clean($_POST['title']) );
 echo "<p>Title:<br />" . $titlee . "</p>";

 ?>



 ********************************************************************************************************/

//[Jj][Aa][Vv][Aa][Ss][Cc][Rr][Ii][Pp][Tt]
DFA *dfaSpecial7(int var, int *indices) {

	dfaSetup(12, var, indices);
	//state 0
	dfaAllocExceptions(2);
	dfaStoreException(1, bintostr('J', var));
	dfaStoreException(1, bintostr('j', var));
	dfaStoreState(11); //sink states

	//state 1
	dfaAllocExceptions(2);
	dfaStoreException(2, bintostr('A', var));
	dfaStoreException(2, bintostr('a', var));
	dfaStoreState(11); //sink states

	//state 2
	dfaAllocExceptions(2);
	dfaStoreException(3, bintostr('V', var));
	dfaStoreException(3, bintostr('v', var));
	dfaStoreState(11); //sink states

	//state 3
	dfaAllocExceptions(2);
	dfaStoreException(4, bintostr('A', var));
	dfaStoreException(4, bintostr('a', var));
	dfaStoreState(11); //sink states

	//state 4
	dfaAllocExceptions(2);
	dfaStoreException(5, bintostr('S', var));
	dfaStoreException(5, bintostr('s', var));
	dfaStoreState(11); //sink states

	//state 5
	dfaAllocExceptions(2);
	dfaStoreException(6, bintostr('C', var));
	dfaStoreException(6, bintostr('c', var));
	dfaStoreState(11); //sink states

	//state 6
	dfaAllocExceptions(2);
	dfaStoreException(7, bintostr('R', var));
	dfaStoreException(7, bintostr('r', var));
	dfaStoreState(11); //sink states

	//state 7
	dfaAllocExceptions(2);
	dfaStoreException(8, bintostr('I', var));
	dfaStoreException(8, bintostr('i', var));
	dfaStoreState(11); //sink states

	//state 8
	dfaAllocExceptions(2);
	dfaStoreException(9, bintostr('P', var));
	dfaStoreException(9, bintostr('p', var));
	dfaStoreState(11); //sink states

	//state 9
	dfaAllocExceptions(2);
	dfaStoreException(10, bintostr('T', var));
	dfaStoreException(10, bintostr('t', var));
	dfaStoreState(11); //sink states

	//state 10
	dfaAllocExceptions(0);
	dfaStoreState(11); //sink states

	//state 11
	dfaAllocExceptions(0);
	dfaStoreState(11); //sink states

	return dfaMinimize(dfaBuild("0000000000+-"));

}

void dfa_test_vul4(int var, int *indices) {
#ifdef _COMPOSITE_ANALYSIS
	DFA* _a; //limit constraint
#endif
	int i = -1;
	int j = 0;
	DFA *M[3];
	DFA *tmpM;

	printf("\n\nSTART Test Vul4!\n");
	//attack strings
	tmpM = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<script ", var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM, dfa_construct_string(">", var, indices),
			var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	//$data = replace("'", "", $data);
	M[0] = dfaAllStringASCIIExceptReserveWords(var, indices);
	M[1] = dfa_construct_string("'", var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "", var, indices);
	//$data = replace('"', "", $data);
	dfaFree(M[1]);
	M[1] = dfaChar('"', var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "", var, indices);
	//$data = replace("\\\\", "\\", $data);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("\\\\", var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "\\", var, indices);

	//$var = ereg_replace( '[Jj][Aa][Vv][Aa][Ss][Cc][Rr][Ii][Pp][Tt]', 'java script', $var );
	dfaFree(M[1]);
	M[1] = dfaSpecial7(var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "java script", var, indices);

	//echo "<p>Title:<br />" . $titlee . "</p>";
	M[2] = dfa_construct_string("<p>Title:<br />", var, indices);
	M[2] = dfa_concat_extrabit(M[1], M[0], var, indices);
	M[2] = dfa_concat_extrabit(M[2], dfa_construct_string("</p>", var, indices),
			var, indices);

	//dfaPrintVitals(M[2]);

#ifdef _COMPOSITE_ANALYSIS
	_a = construct_limit(M[2], var, indices); //limit constraint
#endif

	printf("Memory Allocated: %d\n", mem_allocated());

	i = check_intersection(M[2], tmpM, var, indices);
	if (i == 0)
		printf("Result: Secure!\n");
	else if (i == 1)
		printf("Result: Vulnerable!\n");
	else
		printf("Result: error in dfa_test_vul3() !\n");

	for (j = 0; j < 3; j++) {
		//printf("Delete DFA %d\n", j);
		dfaFree(M[j]);
	}
	dfaFree(tmpM);
}

/***********************************************************************************************
 //Vuln04
 //This is the test prorgram for the following PHP codes

 <?php

 // Simplified version of the vulnerability:
 //   program: aphpkb-0.71
 //    file: global.php, saa.php:18, saa.php:87


 function escdata ($data) {
 $data = replace("'", "", $data);
 $data = replace('"', "", $data);
 $data = replace("\\\\", "\\", $data);
 return $data;
 }

 function xss_clean ($var) {
 $var = ereg_replace( '[Jj][Aa][Vv][Aa][Ss][Cc][Rr][Ii][Pp][Tt]', 'java script', $var );
 $var = ereg_replace("<", "&lt;", $var);
 $var = ereg_replace(">", "&gt;", $var);

 return $var;
 }

 $titlee = escdata(xss_clean($_POST['title']) );
 echo "<p>Title:<br />" . $titlee . "</p>";

 ?>



 ********************************************************************************************************/

void dfa_test_vul4_saint(int var, int *indices) {
#ifdef _COMPOSITE_ANALYSIS
	DFA* _a; //limit constraint
#endif
	int i = -1;
	int j = 0;
	DFA *M[3];
	DFA *tmpM;

	printf("\n\nSTART Test Vul4 Saint!\n");
	//attack strings
	tmpM = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<script ", var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM, dfa_construct_string(">", var, indices),
			var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	//$data = replace("'", "", $data);
	M[0] = dfaAllStringASCIIExceptReserveWords(var, indices);
	M[1] = dfa_construct_string("'", var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "", var, indices);
	//$data = replace('"', "", $data);
	dfaFree(M[1]);
	M[1] = dfaChar('"', var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "", var, indices);
	//$data = replace("\\\\", "\\", $data);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("\\\\", var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "\\", var, indices);

	//$var = ereg_replace( '[Jj][Aa][Vv][Aa][Ss][Cc][Rr][Ii][Pp][Tt]', 'java script', $var );
	dfaFree(M[1]);
	M[1] = dfaSpecial7(var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "java script", var, indices);

	//$var = ereg_replace("<", "&lt;", $var);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("<", var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "&lt", var, indices);

	//$var = ereg_replace(">", "&gt;", $var);
	dfaFree(M[1]);
	M[1] = dfa_construct_string(">", var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "&gt", var, indices);

	//echo "<p>Title:<br />" . $titlee . "</p>";
	M[2] = dfa_construct_string("<p>Title:<br />", var, indices);
	M[2] = dfa_concat_extrabit(M[1], M[0], var, indices);
	M[2] = dfa_concat_extrabit(M[2], dfa_construct_string("</p>", var, indices),
			var, indices);

	//dfaPrintVitals(M[2]);

#ifdef _COMPOSITE_ANALYSIS
	_a = construct_limit(M[2], var, indices); //limit constraint
#endif

	printf("Memory Allocated: %d\n", mem_allocated());

	i = check_intersection(M[2], tmpM, var, indices);
	if (i == 0)
		printf("Result: Secure!\n");
	else if (i == 1)
		printf("Result: Vulnerable!\n");
	else
		printf("Result: error in dfa_test_vul3() !\n");

	for (j = 0; j < 3; j++) {
		//printf("Delete DFA %d\n", j);
		dfaFree(M[j]);
	}
	dfaFree(tmpM);
}

/***********************************************************************************************
 //Vuln05
 //This is the test prorgram for the following PHP codes

 <?php

 // check well-formedness of HTML code:
 //    program: BloggIT 1.0
 //   file: admin.php:23

 //addslashes can be overapproximated as:
 function addslashes ($input) {
 $input = replace("'", "\\'", $input);
 $input = replace("\"", "\\\"", $input);
 $input = replace("\\", "\\\\", $input);
 return $input;
 }


 $cp9 = "A CONSTANT STRING";
 $cp10 = "ANOTHER CONSTANT STRING";

 switch ($_GET["op"]) {
 case "man_ent":
 {
 $sql = "SELECT id,title,date,private FROM blog ORDER BY id DESC";
 $result = mysql_query($sql,$connection);
 while ($row = mysql_fetch_assoc($result))
 {

 $row["title"] = addslashes($row["title"]);
 $row["date"] = addslashes($row["date"]);
 $row["id"] = addslashes($row["id"]);

 print("<tr>\n<td class=\"text\">{$row["date"]}</td>\n<td class=\"text\">{$row["title"]}</td>\n<td align=\"center\">\n");
 if($row["private"])
 {
 print("<a href=\"priv.php?id={$row["id"]}\"><img alt=\"{    $cp9}\" src=\"images/admin/private.gif\" border=\"0\"></a>");
 }
 else
 {
 print("<a href=\"priv.php?id={$row["id"]}\"><img alt=\"{    $cp10}\" src=\"images/admin/public.gif\" border=\"0\"></a>");
 }
 print("</td>");
 }
 break;
 }


 ?>

 //Attack string for print: \Sigma*<script > \Sigma*

 //If we concate all

 ********************************************************************************************************/

void dfa_test_vul5(int var, int *indices) {

#ifdef _COMPOSITE_ANALYSIS
	DFA* _a; //limit constraint
#endif

	int i = -1;
	int j = 0;
	DFA *M[12];
	DFA *tmpM;

	printf("\n\nSTART Test Vul5!\n");
	//attack strings for print
	tmpM = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<script ", var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM, dfa_construct_string(">", var, indices),
			var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	//M[0] $row["title"] = addslashes($row["title"]);
	M[0] = dfaAllStringASCIIExceptReserveWords(var, indices);
	//function addslashes ($input)
	//$input = replace("'", "\\'", $input);

	M[1] = dfa_construct_string("'", var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "\\'", var, indices);
	//$input = replace("\"", "\\\"", $input);
	dfaFree(M[1]);
	M[1] = dfaChar('"', var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "\\\"", var, indices);
	//$input = replace("\\", "\\\\", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("\\", var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "\\\\", var, indices);

	//	printf("\n\nThe result of AddSlash!\n\n");
	//	dfaPrintVerbose(M[0]);

	//M[2] $row["data"] = addslashes($row["date"]);
	M[2] = dfaAllStringASCIIExceptReserveWords(var, indices);
	//function addslashes ($input)
	//$input = replace("'", "\\'", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("'", var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "\\'", var, indices);
	//$input = replace("\"", "\\\"", $input);
	dfaFree(M[1]);
	M[1] = dfaChar('"', var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "\\\"", var, indices);
	//$input = replace("\\", "\\\\", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("\\", var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "\\\\", var, indices);

	//	printf("\n\nThe result of AddSlash!\n\n");
	//	dfaPrintVerbose(M[2]);

	//M[3] $row["id"] = addslashes($row["id"]);
	M[3] = dfaAllStringASCIIExceptReserveWords(var, indices);
	//function addslashes ($input)
	//$input = replace("'", "\\'", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("'", var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "\\'", var, indices);
	//$input = replace("\"", "\\\"", $input);
	dfaFree(M[1]);
	M[1] = dfaChar('"', var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "\\\"", var, indices);
	//$input = replace("\\", "\\\\", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("\\", var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "\\\\", var, indices);

	//	printf("\n\nThe result of AddSlash!\n\n");
	//	dfaPrintVerbose(M[3]);

	//print("<tr>\n<td class=\"text\">{$row["date"]}</td>\n<td class=\"text\">{$row["title"]}</td>\n<td align=\"center\">\n");
	M[4] = dfa_construct_string("<tr>\n<td class=\"text\">", var, indices);
	M[4] = dfa_concat_extrabit(M[4], M[0], var, indices);
	M[4] = dfa_concat_extrabit(M[4],
			dfa_construct_string("</td>\n<td class=\"text\">", var, indices),
			var, indices);
	M[4] = dfa_concat_extrabit(M[4], M[2], var, indices);
	M[4] = dfa_concat_extrabit(M[4],
			dfa_construct_string("</td>\n<td align=\"center\">\n", var,
					indices), var, indices);

	//dfaPrintVitals(M[4]);
	i = check_intersection(M[4], tmpM, var, indices);
	if (i == 0)
		printf("Result1: Secure!\n");
	else if (i == 1)
		printf("Result1: Vulnerable!\n");
	else
		printf("Result1: error in dfa_test_vul5() !\n");

	//print("<a href=\"priv.php?id={$row["id"]}\"><img alt=\"{    $cp9}\" src=\"images/admin/private.gif\" border=\"0\"></a>");
	dfaFree(M[1]);
	M[1] = dfa_construct_string("Show this entry to everybody", var, indices);
	M[5] = dfa_construct_string("<a href=\"priv.php?id=", var, indices);
	M[5] = dfa_concat_extrabit(M[5], M[3], var, indices);
	M[5] = dfa_concat_extrabit(M[5],
			dfa_construct_string("\"><img alt=\"", var, indices), var, indices);
	M[5] = dfa_concat_extrabit(M[5], M[1], var, indices);
	M[5] = dfa_concat_extrabit(M[5],
			dfa_construct_string(
					"\" src=\"images/admin/private.gif\" border=\"0\"></a>",
					var, indices), var, indices);

	//dfaPrintVitals(M[5]);
	i = check_intersection(M[5], tmpM, var, indices);
	if (i == 0)
		printf("Result2: Secure!\n");
	else if (i == 1)
		printf("Result2: Vulnerable!\n");
	else
		printf("Result2: error in dfa_test_vul5() !\n");

	//print("<a href=\"priv.php?id={$row["id"]}\"><img alt=\"{    $cp9}\" src=\"images/admin/private.gif\" border=\"0\"></a>");
	dfaFree(M[1]);
	M[1] = dfa_construct_string("Show this entry only to registered users", var,
			indices);
	M[6] = dfa_construct_string("<a href=\"priv.php?id=", var, indices);
	M[6] = dfa_concat_extrabit(M[6], M[3], var, indices);
	M[6] = dfa_concat_extrabit(M[6],
			dfa_construct_string("\"><img alt=\"", var, indices), var, indices);
	M[6] = dfa_concat_extrabit(M[6], M[1], var, indices);
	M[6] = dfa_concat_extrabit(M[6],
			dfa_construct_string(
					"\" src=\"images/admin/private.gif\" border=\"0\"></a>",
					var, indices), var, indices);

	//dfaPrintVitals(M[6]);
	i = check_intersection(M[6], tmpM, var, indices);
	if (i == 0)
		printf("Result3: Secure!\n");
	else if (i == 1)
		printf("Result3: Vulnerable!\n");
	else
		printf("Result3: error in dfa_test_vul5() !\n");

#ifdef _COMPOSITE_ANALYSIS
	_a = construct_limit(M[6], var, indices); //limit constraint
#endif

	// M[11] the result of print
	M[11] = dfaASCIIOnlyNullString(var, indices); //$result

	M[7] = dfa_concat_extrabit(M[11], M[4], var, indices);
	//if($row["private"])
	M[8] = dfa_concat_extrabit(M[11], M[4], var, indices);
	M[7] = dfa_concat_extrabit(M[7], M[5], var, indices);
	M[8] = dfa_concat_extrabit(M[8], M[6], var, indices);
	M[9] = dfaMinimize(dfaProduct(M[7], M[8], dfaOR));

	M[9] = dfa_concat_extrabit(M[9],
			dfa_construct_string("</td>", var, indices), var, indices);
	M[10] = dfaMinimize(dfaProduct(M[11], M[9], dfaOR)); //the i+1

	printf("Memory Allocated: %d\n", mem_allocated());

	dfaFree(M[11]);
	dfaFree(M[7]);
	dfaFree(M[8]);
	dfaFree(M[9]);

	/*	Iterative Output Result Check
	 i=-1;
	 //Check Valid HTML
	 while(i<1 && j<5){
	 j++;
	 printf("Loop Iteration %d\n", j);
	 M[11] = M[10];
	 M[7] = dfa_concat_extrabit(M[11], M[4], var, indices);
	 //if($row["private"])
	 M[8] = dfa_concat_extrabit(M[11], M[4], var, indices);
	 M[7] = dfa_concat_extrabit(M[7], M[5], var, indices);
	 M[8] = dfa_concat_extrabit(M[8], M[6], var, indices);
	 M[9] = dfaMinimize(dfaProduct(M[7], M[8], dfaOR));
	 M[9] = dfa_concat_extrabit(M[9], dfa_construct_string("</td>", var, indices), var, indices);
	 M[10] = dfaMinimize(dfaProduct(M[11], M[9], dfaOR)); //the i+1

	 //		printf("\n\nBefore Widening:\n", j);
	 //		bddDump(M[10]->bddm);

	 i = check_inclusion(M[10], M[11], var, indices);

	 //		printf("\n\n\Start Widening the following DFA:\n", j);
	 //		bddDump(M[11]->bddm);
	 //dfaPrintVerbose(M[11]);
	 //		Use widening
	 //		Widening Failed in this case
	 //		M[10]=dfaWiden(M[11], M[10]);
	 dfaFree(M[11]);
	 dfaFree(M[7]);
	 dfaFree(M[8]);
	 dfaFree(M[9]);
	 }
	 */

	for (j = 0; j < 12; j++) {
		//printf("Delete DFA %d\n", j);
		if (j != 7 && j != 8 && j != 9 && j != 11)
			dfaFree(M[j]);
	}
	dfaFree(tmpM);
}

/***********************************************************************************************
 //Vuln05 Saint
 //This is the test prorgram for the following PHP codes

 <?php

 // check well-formedness of HTML code:
 //    program: BloggIT 1.0
 //   file: admin.php:23

 //addslashes can be overapproximated as:
 function addslashes ($input) {
 $input = replace("'", "\\'", $input);
 $input = replace("\"", "\\\"", $input);
 $input = replace("\\", "\\\\", $input);
 return $input;
 }


 $cp9 = "A CONSTANT STRING";
 $cp10 = "ANOTHER CONSTANT STRING";

 switch ($_GET["op"]) {
 case "man_ent":
 {
 $sql = "SELECT id,title,date,private FROM blog ORDER BY id DESC";
 $result = mysql_query($sql,$connection);
 while ($row = mysql_fetch_assoc($result))
 {

 $row["title"] = addslashes($row["title"]);
 $row["title"] = ereg_replace("<", "&lt;", $row["title"]);
 $row["title"] = ereg_replace(">", "&gt;", $row["title"]);
 $row["date"] = addslashes($row["date"]);
 $row["date"] = ereg_replace("<", "&lt;", $row["date"]);
 $row["date"] = ereg_replace(">", "&gt;", $row["date"]);
 $row["id"] = addslashes($row["id"]);
 $row["id"] = ereg_replace("<", "&lt;", $row["id"]);
 $row["id"] = ereg_replace(">", "&gt;", $row["id"]);
 print("<tr>\n<td class=\"text\">{$row["date"]}</td>\n<td class=\"text\">{$row["title"]}</td>\n<td align=\"center\">\n");
 if($row["private"])
 {
 print("<a href=\"priv.php?id={$row["id"]}\"><img alt=\"{    $cp9}\" src=\"images/admin/private.gif\" border=\"0\"></a>");
 }
 else
 {
 print("<a href=\"priv.php?id={$row["id"]}\"><img alt=\"{    $cp10}\" src=\"images/admin/public.gif\" border=\"0\"></a>");
 }
 print("</td>");
 }
 break;
 }


 ?>

 //Attack string for print: \Sigma*<script > \Sigma*

 //If we concate all

 ********************************************************************************************************/

void dfa_test_vul5_saint(int var, int *indices) {

#ifdef _COMPOSITE_ANALYSIS
	DFA* _a; //limit constraint
#endif

	int i = -1;
	int j = 0;
	DFA *M[12];
	DFA *tmpM;

	printf("\n\nSTART Test Vul5 Saint!\n");
	//attack strings for print
	tmpM = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<script ", var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM, dfa_construct_string(">", var, indices),
			var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	//M[0] $row["title"] = addslashes($row["title"]);
	M[0] = dfaAllStringASCIIExceptReserveWords(var, indices);
	//function addslashes ($input)
	//$input = replace("'", "\\'", $input);

	M[1] = dfa_construct_string("'", var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "\\'", var, indices);
	//$input = replace("\"", "\\\"", $input);
	dfaFree(M[1]);
	M[1] = dfaChar('"', var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "\\\"", var, indices);
	//$input = replace("\\", "\\\\", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("\\", var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "\\\\", var, indices);

	//ADD SANITIZED FUNCTION
	//$var = ereg_replace("<", "&lt;", $var);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("<", var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "&lt", var, indices);
	//$var = ereg_replace(">", "&gt;", $var);
	dfaFree(M[1]);
	M[1] = dfa_construct_string(">", var, indices);
	M[0] = dfa_replace_extrabit(M[0], M[1], "&gt", var, indices);

	//	printf("\n\nThe result of AddSlash!\n\n");
	//	dfaPrintVerbose(M[0]);

	//M[2] $row["data"] = addslashes($row["date"]);
	M[2] = dfaAllStringASCIIExceptReserveWords(var, indices);
	//function addslashes ($input)
	//$input = replace("'", "\\'", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("'", var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "\\'", var, indices);
	//$input = replace("\"", "\\\"", $input);
	dfaFree(M[1]);
	M[1] = dfaChar('"', var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "\\\"", var, indices);
	//$input = replace("\\", "\\\\", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("\\", var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "\\\\", var, indices);

	//ADD SANITIZED FUNCTION
	//$var = ereg_replace("<", "&lt;", $var);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("<", var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "&lt", var, indices);
	//$var = ereg_replace(">", "&gt;", $var);
	dfaFree(M[1]);
	M[1] = dfa_construct_string(">", var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "&gt", var, indices);

	//	printf("\n\nThe result of AddSlash!\n\n");
	//	dfaPrintVerbose(M[2]);

	//M[3] $row["id"] = addslashes($row["id"]);
	M[3] = dfaAllStringASCIIExceptReserveWords(var, indices);
	//function addslashes ($input)
	//$input = replace("'", "\\'", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("'", var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "\\'", var, indices);
	//$input = replace("\"", "\\\"", $input);
	dfaFree(M[1]);
	M[1] = dfaChar('"', var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "\\\"", var, indices);
	//$input = replace("\\", "\\\\", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("\\", var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "\\\\", var, indices);

	//ADD SANITIZED FUNCTION
	//$var = ereg_replace("<", "&lt;", $var);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("<", var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "&lt", var, indices);
	//$var = ereg_replace(">", "&gt;", $var);
	dfaFree(M[1]);
	M[1] = dfa_construct_string(">", var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "&gt", var, indices);

	//	printf("\n\nThe result of AddSlash!\n\n");
	//	dfaPrintVerbose(M[3]);

	//print("<tr>\n<td class=\"text\">{$row["date"]}</td>\n<td class=\"text\">{$row["title"]}</td>\n<td align=\"center\">\n");
	M[4] = dfa_construct_string("<tr>\n<td class=\"text\">", var, indices);
	M[4] = dfa_concat_extrabit(M[4], M[0], var, indices);
	M[4] = dfa_concat_extrabit(M[4],
			dfa_construct_string("</td>\n<td class=\"text\">", var, indices),
			var, indices);
	M[4] = dfa_concat_extrabit(M[4], M[2], var, indices);
	M[4] = dfa_concat_extrabit(M[4],
			dfa_construct_string("</td>\n<td align=\"center\">\n", var,
					indices), var, indices);

	//dfaPrintVitals(M[4]);
	i = check_intersection(M[4], tmpM, var, indices);
	if (i == 0)
		printf("Result1: Secure!\n");
	else if (i == 1)
		printf("Result1: Vulnerable!\n");
	else
		printf("Result1: error in dfa_test_vul5() !\n");

	//print("<a href=\"priv.php?id={$row["id"]}\"><img alt=\"{    $cp9}\" src=\"images/admin/private.gif\" border=\"0\"></a>");
	dfaFree(M[1]);
	M[1] = dfa_construct_string("Show this entry to everybody", var, indices);
	M[5] = dfa_construct_string("<a href=\"priv.php?id=", var, indices);
	M[5] = dfa_concat_extrabit(M[5], M[3], var, indices);
	M[5] = dfa_concat_extrabit(M[5],
			dfa_construct_string("\"><img alt=\"", var, indices), var, indices);
	M[5] = dfa_concat_extrabit(M[5], M[1], var, indices);
	M[5] = dfa_concat_extrabit(M[5],
			dfa_construct_string(
					"\" src=\"images/admin/private.gif\" border=\"0\"></a>",
					var, indices), var, indices);

	//dfaPrintVitals(M[5]);
	i = check_intersection(M[5], tmpM, var, indices);
	if (i == 0)
		printf("Result2: Secure!\n");
	else if (i == 1)
		printf("Result2: Vulnerable!\n");
	else
		printf("Result2: error in dfa_test_vul5() !\n");

	//print("<a href=\"priv.php?id={$row["id"]}\"><img alt=\"{    $cp9}\" src=\"images/admin/private.gif\" border=\"0\"></a>");
	dfaFree(M[1]);
	M[1] = dfa_construct_string("Show this entry only to registered users", var,
			indices);
	M[6] = dfa_construct_string("<a href=\"priv.php?id=", var, indices);
	M[6] = dfa_concat_extrabit(M[6], M[3], var, indices);
	M[6] = dfa_concat_extrabit(M[6],
			dfa_construct_string("\"><img alt=\"", var, indices), var, indices);
	M[6] = dfa_concat_extrabit(M[6], M[1], var, indices);
	M[6] = dfa_concat_extrabit(M[6],
			dfa_construct_string(
					"\" src=\"images/admin/private.gif\" border=\"0\"></a>",
					var, indices), var, indices);

	//dfaPrintVitals(M[6]);
	i = check_intersection(M[6], tmpM, var, indices);
	if (i == 0)
		printf("Result3: Secure!\n");
	else if (i == 1)
		printf("Result3: Vulnerable!\n");
	else
		printf("Result3: error in dfa_test_vul5() !\n");

#ifdef _COMPOSITE_ANALYSIS
	_a = construct_limit(M[6], var, indices); //limit constraint
#endif

	// M[11] the result of print
	M[11] = dfaASCIIOnlyNullString(var, indices); //$result

	M[7] = dfa_concat_extrabit(M[11], M[4], var, indices);
	//if($row["private"])
	M[8] = dfa_concat_extrabit(M[11], M[4], var, indices);
	M[7] = dfa_concat_extrabit(M[7], M[5], var, indices);
	M[8] = dfa_concat_extrabit(M[8], M[6], var, indices);
	M[9] = dfaMinimize(dfaProduct(M[7], M[8], dfaOR));

	M[9] = dfa_concat_extrabit(M[9],
			dfa_construct_string("</td>", var, indices), var, indices);
	M[10] = dfaMinimize(dfaProduct(M[11], M[9], dfaOR)); //the i+1

	printf("Memory Allocated: %d\n", mem_allocated());

	dfaFree(M[11]);
	dfaFree(M[7]);
	dfaFree(M[8]);
	dfaFree(M[9]);

	/* // Iterative Output result check
	 i=-1;
	 //Check Valid HTML
	 while(i<1 && j<5){
	 j++;
	 printf("Loop Iteration %d\n", j);
	 M[11] = M[10];
	 M[7] = dfa_concat_extrabit(M[11], M[4], var, indices);
	 //if($row["private"])
	 M[8] = dfa_concat_extrabit(M[11], M[4], var, indices);
	 M[7] = dfa_concat_extrabit(M[7], M[5], var, indices);
	 M[8] = dfa_concat_extrabit(M[8], M[6], var, indices);
	 M[9] = dfaMinimize(dfaProduct(M[7], M[8], dfaOR));
	 M[9] = dfa_concat_extrabit(M[9], dfa_construct_string("</td>", var, indices), var, indices);
	 M[10] = dfaMinimize(dfaProduct(M[11], M[9], dfaOR)); //the i+1

	 //		printf("\n\nBefore Widening:\n", j);
	 //		bddDump(M[10]->bddm);

	 i = check_inclusion(M[10], M[11], var, indices);

	 //		printf("\n\n\Start Widening the following DFA:\n", j);
	 //		bddDump(M[11]->bddm);
	 //dfaPrintVerbose(M[11]);
	 //		Use widening
	 //		Widening Failed in this case
	 //		M[10]=dfaWiden(M[11], M[10]);
	 dfaFree(M[11]);
	 dfaFree(M[7]);
	 dfaFree(M[8]);
	 dfaFree(M[9]);
	 }
	 */

	for (j = 0; j < 12; j++) {
		//printf("Delete DFA %d\n", j);
		if (j != 7 && j != 8 && j != 9 && j != 11)
			dfaFree(M[j]);
	}
	dfaFree(tmpM);
}

/***********************************************************************************************
 //Vuln06
 //This is the test prorgram for the following PHP codes

 <?php

 // simplified correct sanitization for $message, incorrect for $from:
 //    program: proManager-0.72
 //    file: message.php:91


 function default_font ($texto) {

 $default_font_face = "Arial, Helvetica, Sans-serif";
 $default_font_size = 2;

 return  "<font face=\"$default_font_face\" size=$default_font_size>".
 $texto.
 "</font>";
 }

 $id = 0;
 $strFrom = "From";

 // nl2br can be overapproximated as:
 //    $input = replace("\\n", "<br/>", $input)

 $message = nl2br($_GET["message"]);

 $message = str_replace (":O", "<img src=\"images/eek.gif\">", $message);
 $message = str_replace (":-O", "<img src=\"images/eek.gif\">", $message);
 $message = ereg_replace ("\:\)\)+", "<img src=\"images/grin.gif\">", $message);
 $message = ereg_replace ("\:\-\)\)+", "<img src=\"images/grin.gif\">", $message);
 $message = str_replace (":)", "<img src=\"images/smile.gif\">", $message);
 $message = str_replace (":-)", "<img src=\"images/smile.gif\">", $message);
 $message = ereg_replace (">:\(+", "<img src=\"images/g.gif\">", $message);
 $message = ereg_replace (">:-\(+", "<img src=\"images/g.gif\">", $message);
 $message = ereg_replace ("\:\(\(+", "<img src=\"images/angry.gif\">", $message);
 $message = ereg_replace ("\:\-\(\(+", "<img src=\"images/angry.gif\">", $message);
 $message = str_replace (":(", "<img src=\"images/sad.gif\">", $message);
 $message = str_replace (":-(", "<img src=\"images/sad.gif\">", $message);
 $message = str_replace (";)", "<img src=\"images/wink.gif\">", $message);
 $message = str_replace (";-)", "<img src=\"images/wink.gif\">", $message);

 // SCRIPT_NAME can be overapproximated by
 //    [0-9a-zA-Z/]+

 if ($hardhtml == 1) {
 $message = ereg_replace(">","&gt;",$message);
 $message = ereg_replace("<","&lt;",$message);
 $message = ereg_replace("&lt;br&gt;","<br>",$message);

 $insert = "ASCII | <A href=\"$SCRIPT_NAME?id=$id&hardhtml=0\">HTML</a>";
 }
 else {
 $insert = "<a href=\"$SCRIPT_NAME?id=$id&hardhtml=1\">ASCII</a> | HTML";
 }

 // addslashes can be overapproximated as:
 //    $input = replace("'", "\\'", $input);
 //    $input = replace("\"", "\\\"", $input);
 //    $input = replace("\\", "\\\\", $input);

 $name = addslashes($_GET["name"]);
 $username = addslashes($_GET["username"]);
 $from = "$name ($username)";

 $content = "
 <font face=\"Arial, Helvetica, Sans-serif\" size=2>
 <div align=right><b>
 <font face=\"Verdana, Helvetica, Sans-serif\" size=1>$insert</font>
 </b></div>
 <b>$strFrom:</b> $from<br><br>
 <br>$message<br>";

 echo default_font($content);


 ?>

 //Attack string for print: \Sigma*<script > \Sigma*

 //If we concate all

 ********************************************************************************************************/

//)+
DFA *dfaSpecial6_1(int var, int* indices) {

	char a = ')';
	dfaSetup(3, var, indices);
	dfaAllocExceptions(1);
	dfaStoreException(1, bintostr((unsigned long) a, var));
	dfaStoreState(2);

	//state 1
	dfaAllocExceptions(1);
	dfaStoreException(1, bintostr((unsigned long) a, var));
	dfaStoreState(2);

	//state 2
	dfaAllocExceptions(0);
	dfaStoreState(2);

	return dfaBuild("0+-");
}

//[0-9a-zA-Z/]+
DFA *dfaSpecial6_2(int var, int* indices) {
	unsigned long n;
	char a = '/';
	dfaSetup(3, var, indices);
	dfaAllocExceptions(63);
	dfaStoreException(1, bintostr((unsigned long) a, var));
	for (n = 48; n <= 57; n++)
		dfaStoreException(1, bintostr(n, var));
	for (n = 65; n <= 90; n++)
		dfaStoreException(1, bintostr(n, var));
	for (n = 97; n <= 122; n++)
		dfaStoreException(1, bintostr(n, var));
	dfaStoreState(2);

	//state 1
	dfaAllocExceptions(63);
	dfaStoreException(1, bintostr((unsigned long) a, var));
	for (n = 48; n <= 57; n++)
		dfaStoreException(1, bintostr(n, var));
	for (n = 65; n <= 90; n++)
		dfaStoreException(1, bintostr(n, var));
	for (n = 97; n <= 122; n++)
		dfaStoreException(1, bintostr(n, var));
	dfaStoreState(2);

	//state 2
	dfaAllocExceptions(0);
	dfaStoreState(2);

	return dfaBuild("0+-");
}

//(+
DFA *dfaSpecial6_3(int var, int* indices) {

	char a = '(';
	dfaSetup(3, var, indices);
	dfaAllocExceptions(1);
	dfaStoreException(1, bintostr((unsigned long) a, var));
	dfaStoreState(2);

	//state 1
	dfaAllocExceptions(1);
	dfaStoreException(1, bintostr((unsigned long) a, var));
	dfaStoreState(2);

	//state 2
	dfaAllocExceptions(0);
	dfaStoreState(2);

	return dfaBuild("0+-");
}

void dfa_test_vul6(int var, int *indices) {

#ifdef _COMPOSITE_ANALYSIS
	DFA* _a; //limit constraint
#endif

	int i = -1;
	int j = 0;
	DFA *M[6];
	DFA *C[2];
	DFA *tmpM;
	DFA *freeM;

	printf("\n\nSTART Test Vul6!\n");
	//attack strings for echo
	tmpM = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<script ", var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM, dfa_construct_string(">", var, indices),
			var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	//$id = 0;
	C[0] = dfaChar('0', var, indices);

	//$strFrom = "From";
	C[1] = dfa_construct_string("From", var, indices);

	// M[0] is $message, M[1] and M[2] are used as temp variable
	//$message = nl2br($_GET["message"]);
	// nl2br can be overapproximated as:
	//$input = replace("\\n", "<br/>", $input)

	// In the following, we ignore $message in this example

	M[0] = dfaAllStringASCIIExceptReserveWords(var, indices);
	M[1] = dfa_construct_string("\\n", var, indices);
	freeM = M[0];
	M[0] = dfa_replace_extrabit(M[0], M[1], "<br/>", var, indices);
	dfaFree(freeM);

	//$message = str_replace (":O", "<img src=\"images/eek.gif\">", $message);
	dfaFree(M[1]);
	M[1] = dfaProduct(dfa_construct_string(":O", var, indices),
			dfa_construct_string(":-O", var, indices), dfaOR);
	dfaMinimize(M[1]);
	dfaPrintVerbose(M[1]);
	freeM = M[0];
	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/eek.gif\">", var,
			indices);
	dfaFree(freeM);
	printf("\nEnd of Union\n");
	//$message = str_replace (":-O", "<img src=\"images/eek.gif\">", $message);
	//	dfaFree(M[1]);
	//	M[1] = dfa_construct_string(":-O", var, indices);
	//	freeM=M[0];
	//	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/eek.gif\">", var, indices);
	//	dfaFree(freeM);

	//$message = ereg_replace ("\:\)\)+", "<img src=\"images/grin.gif\">", $message);
	dfaFree(M[1]);
	M[1] = dfaProduct(dfa_construct_string(":)", var, indices),
			dfa_construct_string(":-)", var, indices), dfaOR);
	dfaMinimize(M[1]);
	//M[1] = dfa_construct_string(":)", var, indices);
	M[2] = dfaSpecial6_1(var, indices);
	M[1] = dfa_concat_extrabit(M[1], M[2], var, indices);
	freeM = M[0];
	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/grin.gif\">",
			var, indices);
	dfaFree(freeM);

	//	dfaPrintVitals(M[0]);
	//$message = ereg_replace ("\:\-\)\)+", "<img src=\"images/grin.gif\">", $message);
	//	dfaFree(M[1]);
	//	dfaFree(M[2]);
	//	M[1] = dfa_construct_string(":-)", var, indices);
	//	M[2] = dfaSpecial6_1(var, indices);
	//	M[1] = dfa_concat_extrabit(M[1], M[2], var, indices);
	//	freeM=M[0];
	//	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/grin.gif\">", var, indices);
	//	dfaFree(freeM);

	//$message = str_replace (":)", "<img src=\"images/smile.gif\">", $message);
	dfaFree(M[1]);
	M[1] = dfaProduct(dfa_construct_string(":)", var, indices),
			dfa_construct_string(":-)", var, indices), dfaOR);
	//	M[1] = dfa_construct_string(":)", var, indices);
	freeM = M[0];
	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/smile.gif\">",
			var, indices);
	dfaFree(freeM);

	//	dfaPrintVitals(M[0]);

	//$message = str_replace (":-)", "<img src=\"images/smile.gif\">", $message);
	//	dfaFree(M[1]);
	//	M[1] = dfa_construct_string(":-)", var, indices);
	//	freeM=M[0];
	//	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/smile.gif\">", var, indices);
	//	dfaFree(freeM);
	/*
	 //$message = ereg_replace (">:\(+", "<img src=\"images/g.gif\">", $message);
	 dfaFree(M[1]);
	 dfaFree(M[2]);
	 M[1] = dfaProduct(dfa_construct_string(">:", var, indices), dfa_construct_string(">:-", var, indices), dfaOR);
	 dfaMinimize(M[1]);
	 //	M[1] = dfa_construct_string(">:", var, indices);
	 M[2] = dfaSpecial6_3(var, indices);
	 freeM=M[1];
	 M[1] = dfa_concat_extrabit(M[1], M[2], var, indices);
	 dfaFree(freeM);
	 freeM=M[0];
	 M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/g.gif\">", var, indices);
	 dfaFree(freeM);

	 printf("\nEnd of Union3\n");

	 //
	 //$message = ereg_replace (">:-\(+", "<img src=\"images/g.gif\">", $message);
	 //	dfaFree(M[1]);
	 //	dfaFree(M[2]);
	 //	M[1] = dfa_construct_string(">:-", var, indices);
	 //	M[2] = dfaSpecial6_3(var, indices);
	 //	M[1] = dfa_concat_extrabit(M[1], M[2], var, indices);
	 //	dfaPrintVerbose(M[1]);
	 //	freeM=M[0];
	 //	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/g.gif\">", var, indices);
	 //	dfaFree(freeM);


	 //$message = ereg_replace ("\:\(\(+", "<img src=\"images/angry.gif\">", $message);
	 dfaFree(M[1]);
	 dfaFree(M[2]);
	 M[1] = dfaProduct(dfa_construct_string(":-", var, indices), dfa_construct_string(":", var, indices), dfaOR);
	 //	dfaMinimize(M[1]);
	 //	M[1] = dfa_construct_string(":(", var, indices);
	 M[2] = dfaSpecial6_3(var, indices);
	 //	dfaPrintVerbose(M[1]);
	 M[1] = dfa_concat_extrabit(M[1], M[2], var, indices);
	 freeM=M[0];
	 M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/angry.gif\">", var, indices);
	 dfaFree(freeM);

	 //$message = ereg_replace ("\:\-\(\(+", "<img src=\"images/angry.gif\">", $message);
	 //	dfaFree(M[1]);
	 //	dfaFree(M[2]);
	 //	M[1] = dfa_construct_string(":-(", var, indices);
	 //	M[2] = dfaSpecial6_3(var, indices);
	 //	M[1] = dfa_concat_extrabit(M[1], M[2], var, indices);
	 //	freeM=M[0];
	 //	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/angry.gif\">", var, indices);
	 //	dfaFree(freeM);


	 //$message = str_replace (":(", "<img src=\"images/sad.gif\">", $message);
	 dfaFree(M[1]);
	 M[1] = dfaProduct(dfa_construct_string(":(", var, indices), dfa_construct_string(":-(", var, indices), dfaOR);
	 //	M[1] = dfa_construct_string(":(", var, indices);
	 freeM=M[0];
	 M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/sad.gif\">", var, indices);
	 dfaFree(freeM);


	 //$message = str_replace (":-(", "<img src=\"images/sad.gif\">", $message);
	 //	dfaFree(M[1]);
	 //	M[1] = dfa_construct_string(":-(", var, indices);
	 //	freeM=M[0];
	 //	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/sad.gif\">", var, indices);
	 //	dfaFree(freeM);


	 //$message = str_replace (";)", "<img src=\"images/wink.gif\">", $message);
	 dfaFree(M[1]);
	 M[1] = dfaProduct(dfa_construct_string(";)", var, indices), dfa_construct_string(";-)", var, indices), dfaOR);
	 dfaMinimize(M[1]);
	 //	M[1] = dfa_construct_string(";)", var, indices);
	 freeM=M[0];
	 M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/wink.gif\">", var, indices);
	 dfaFree(freeM);

	 //$message = str_replace (";-)", "<img src=\"images/wink.gif\">", $message);
	 //	dfaFree(M[1]);
	 //	M[1] = dfa_construct_string(";-)", var, indices);
	 //	freeM=M[0];
	 //	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/wink.gif\">", var, indices);
	 //	dfaFree(freeM);

	 //	dfaPrintVerbose(M[0]);
	 */

	//printf("\nEND of BLOCK 1\n\n");
	//Block 2: if branch
	//M[3] is $message
	//$message = ereg_replace(">","&gt;",$message);
	dfaFree(M[1]);
	M[1] = dfa_construct_string(">", var, indices);
	M[3] = dfa_replace_extrabit(M[0], M[1], "&gt;", var, indices);

	//$message = ereg_replace("<","&lt;",$message);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("<", var, indices);
	freeM = M[3];
	M[3] = dfa_replace_extrabit(M[3], M[1], "&lt;", var, indices);
	dfaFree(freeM);

	//$message = ereg_replace("&lt;br&gt;","<br>",$message);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("&lt;br&gt;", var, indices);
	freeM = M[3];
	M[3] = dfa_replace_extrabit(M[3], M[1], "<br>", var, indices);
	dfaFree(freeM);

	//M[4] as $insert
	//$insert = "ASCII | <A href=\"$SCRIPT_NAME?id=$id&hardhtml=0\">HTML</a>";
	dfaFree(M[1]);
	M[1] = dfaSpecial6_2(var, indices); //$SCRIPT_NAME
	M[4] = dfa_construct_string("ASCII | <A href=\"", var, indices);
	M[4] = dfa_concat_extrabit(M[4], M[1], var, indices);
	M[4] = dfa_concat_extrabit(M[4], dfa_construct_string("?id=", var, indices),
			var, indices);
	M[4] = dfa_concat_extrabit(M[4], C[0], var, indices);
	M[4] = dfa_concat_extrabit(M[4],
			dfa_construct_string("&hardhtml=0\">HTML</a>", var, indices), var,
			indices);

	//Block 3: else branch
	//M[5] as $insert
	//$insert = "<a href=\"$SCRIPT_NAME?id=$id&hardhtml=1\">ASCII</a> | HTML";
	dfaFree(M[1]);
	M[1] = dfaSpecial6_2(var, indices); //$SCRIPT_NAME
	M[5] = dfa_construct_string("<a href=\"", var, indices);
	M[5] = dfa_concat_extrabit(M[5], M[1], var, indices);
	M[5] = dfa_concat_extrabit(M[5], dfa_construct_string("?id=", var, indices),
			var, indices);
	M[5] = dfa_concat_extrabit(M[5], C[0], var, indices);
	M[5] = dfa_concat_extrabit(M[5],
			dfa_construct_string("&hardhtml=1\">ASCII</a> | HTML", var,
					indices), var, indices);

	//Block 4: Union both branches
	//M[0] as $message
	//M[4] as $insert
	freeM = M[0];
	M[0] = dfaMinimize(dfaProduct(M[0], M[3], dfaOR));
	dfaFree(freeM);

	freeM = M[4];
	M[4] = dfaMinimize(dfaProduct(M[4], M[5], dfaOR));
	dfaFree(freeM);

	//M[2] as $name
	//$name = addslashes($_GET["name"]);
	//dfaFree(M[2]);
	dfaFree(M[1]);
	//M[0] $row["title"] = addslashes($row["title"]);
	M[2] = dfaAllStringASCIIExceptReserveWords(var, indices);
	//function addslashes ($input)
	//$input = replace("'", "\\'", $input);

	M[1] = dfa_construct_string("'", var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "\\'", var, indices);
	//$input = replace("\"", "\\\"", $input);
	dfaFree(M[1]);
	M[1] = dfaChar('"', var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "\\\"", var, indices);
	//$input = replace("\\", "\\\\", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("\\", var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "\\\\", var, indices);

	//M[3] as $username
	//$username = addslashes($_GET["username"]);
	dfaFree(M[3]);
	dfaFree(M[1]);
	//M[0] $row["title"] = addslashes($row["title"]);
	M[3] = dfaAllStringASCIIExceptReserveWords(var, indices);
	//function addslashes ($input)
	//$input = replace("'", "\\'", $input);

	M[1] = dfa_construct_string("'", var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "\\'", var, indices);
	//$input = replace("\"", "\\\"", $input);
	dfaFree(M[1]);
	M[1] = dfaChar('"', var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "\\\"", var, indices);
	//$input = replace("\\", "\\\\", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("\\", var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "\\\\", var, indices);

	//M[5] as $from
	//$from = "$name ($username)";
	dfaFree(M[5]);
	M[5] = dfa_concat_extrabit(M[2], dfa_construct_string(" (", var, indices),
			var, indices);
	M[5] = dfa_concat_extrabit(M[5], M[3], var, indices);
	M[5] = dfa_concat_extrabit(M[5], dfa_construct_string(")", var, indices),
			var, indices);

	//M[2] as $content
	/*$content = "
	 <font face=\"Arial, Helvetica, Sans-serif\" size=2>
	 <div align=right><b>
	 <font face=\"Verdana, Helvetica, Sans-serif\" size=1>$insert</font>
	 </b></div>
	 <b>$strFrom:</b> $from<br><br>
	 <br>$message<br>";
	 */
	dfaFree(M[2]);
	M[2] =
			dfa_construct_string(
					"       <font face=\"Arial, Helvetica, Sans-serif\" size=2>\n       <div align=right><b>\n       <font face=\"Verdana, Helvetica, Sans-serif\" size=1>",
					var, indices);

	M[2] = dfa_concat_extrabit(M[2], M[4], var, indices); //M[4] is $insert
	M[2] = dfa_concat_extrabit(M[2],
			dfa_construct_string("</font>\n       </b></div>\n       <b>", var,
					indices), var, indices);
	M[2] = dfa_concat_extrabit(M[2], C[1], var, indices); //C[1] is $strFrom
	M[2] = dfa_concat_extrabit(M[2],
			dfa_construct_string(":</b> ", var, indices), var, indices);
	M[2] = dfa_concat_extrabit(M[2], M[5], var, indices); //M[5] is $from
	M[2] = dfa_concat_extrabit(M[2],
			dfa_construct_string("<br><br>\n       <br>", var, indices), var,
			indices);
	M[2] = dfa_concat_extrabit(M[2], M[0], var, indices); //M[0] is $message
	M[2] = dfa_concat_extrabit(M[2], dfa_construct_string("<br>", var, indices),
			var, indices);

	//echo default_font($content);
	/*
	 function default_font ($texto) {

	 $default_font_face = "Arial, Helvetica, Sans-serif";
	 $default_font_size = 2;

	 return  "<font face=\"$default_font_face\" size=$default_font_size>".
	 $texto.
	 "</font>";
	 }
	 */

	//$default_font_face = "Arial, Helvetica, Sans-serif";
	dfaFree(M[0]);
	M[0] = dfa_construct_string("Arial, Helvetica, Sans-serif", var, indices);
	//$default_font_size = 2;
	dfaFree(M[1]);
	M[1] = dfa_construct_string("2", var, indices);
	//M[3] as return value of
	dfaFree(M[3]);
	M[3] = dfa_construct_string("<font face=\"", var, indices);
	M[3] = dfa_concat_extrabit(M[3], M[0], var, indices); //M[0] is $default_font_face
	M[3] = dfa_concat_extrabit(M[3],
			dfa_construct_string(" size=", var, indices), var, indices);
	M[3] = dfa_concat_extrabit(M[3], M[1], var, indices); //M[1] is $default_font_size
	M[3] = dfa_concat_extrabit(M[3], dfa_construct_string(">", var, indices),
			var, indices);
	M[3] = dfa_concat_extrabit(M[3], M[2], var, indices); //M[2] is $texto
	M[3] = dfa_concat_extrabit(M[3],
			dfa_construct_string("</font>", var, indices), var, indices);

	//dfaPrintVitals(M[3]);

	i = check_intersection(M[3], tmpM, var, indices);
	if (i == 0)
		printf("Result: Secure!\n");
	else if (i == 1)
		printf("Result: Vulnerable!\n");
	else
		printf("Result: error in dfa_test_vul6() !\n");

#ifdef _COMPOSITE_ANALYSIS
	_a = construct_limit(M[3], var, indices); //limit constraint
#endif

	printf("Memory Allocated: %d\n", mem_allocated());

	for (j = 0; j < 6; j++) {
		//printf("Delete DFA %d\n", j);
		dfaFree(M[j]);
	}
	dfaFree(tmpM);
	dfaFree(C[0]);
	dfaFree(C[1]);
}

void dfa_test_vul6_saint(int var, int *indices) {

#ifdef _COMPOSITE_ANALYSIS
	DFA* _a; //limit constraint
#endif

	int i = -1;
	int j = 0;
	DFA *M[6];
	DFA *C[2];
	DFA *tmpM;
	DFA *freeM;

	printf("\n\nSTART Test Vul6 Saint!\n");
	//attack strings for echo
	tmpM = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<script ", var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);
	tmpM = dfa_concat_extrabit(tmpM, dfa_construct_string(">", var, indices),
			var, indices);
	tmpM = dfa_concat_extrabit(tmpM,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	//$id = 0;
	C[0] = dfaChar('0', var, indices);

	//$strFrom = "From";
	C[1] = dfa_construct_string("From", var, indices);

	// M[0] is $message, M[1] and M[2] are used as temp variable
	//$message = nl2br($_GET["message"]);
	// nl2br can be overapproximated as:
	//$input = replace("\\n", "<br/>", $input)

	// In the following, we ignore $message in this example

	M[0] = dfaAllStringASCIIExceptReserveWords(var, indices);
	M[1] = dfa_construct_string("\\n", var, indices);
	freeM = M[0];
	M[0] = dfa_replace_extrabit(M[0], M[1], "<br/>", var, indices);
	dfaFree(freeM);

	//$message = str_replace (":O", "<img src=\"images/eek.gif\">", $message);
	dfaFree(M[1]);
	M[1] = dfaProduct(dfa_construct_string(":O", var, indices),
			dfa_construct_string(":-O", var, indices), dfaOR);
	dfaMinimize(M[1]);
	dfaPrintVerbose(M[1]);
	freeM = M[0];
	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/eek.gif\">", var,
			indices);
	dfaFree(freeM);
	printf("\nEnd of Union\n");
	//$message = str_replace (":-O", "<img src=\"images/eek.gif\">", $message);
	//	dfaFree(M[1]);
	//	M[1] = dfa_construct_string(":-O", var, indices);
	//	freeM=M[0];
	//	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/eek.gif\">", var, indices);
	//	dfaFree(freeM);

	//$message = ereg_replace ("\:\)\)+", "<img src=\"images/grin.gif\">", $message);
	dfaFree(M[1]);
	M[1] = dfaProduct(dfa_construct_string(":)", var, indices),
			dfa_construct_string(":-)", var, indices), dfaOR);
	dfaMinimize(M[1]);
	//M[1] = dfa_construct_string(":)", var, indices);
	M[2] = dfaSpecial6_1(var, indices);
	M[1] = dfa_concat_extrabit(M[1], M[2], var, indices);
	freeM = M[0];
	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/grin.gif\">",
			var, indices);
	dfaFree(freeM);

	//	dfaPrintVitals(M[0]);
	//$message = ereg_replace ("\:\-\)\)+", "<img src=\"images/grin.gif\">", $message);
	//	dfaFree(M[1]);
	//	dfaFree(M[2]);
	//	M[1] = dfa_construct_string(":-)", var, indices);
	//	M[2] = dfaSpecial6_1(var, indices);
	//	M[1] = dfa_concat_extrabit(M[1], M[2], var, indices);
	//	freeM=M[0];
	//	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/grin.gif\">", var, indices);
	//	dfaFree(freeM);

	//$message = str_replace (":)", "<img src=\"images/smile.gif\">", $message);
	dfaFree(M[1]);
	M[1] = dfaProduct(dfa_construct_string(":)", var, indices),
			dfa_construct_string(":-)", var, indices), dfaOR);
	//	M[1] = dfa_construct_string(":)", var, indices);
	freeM = M[0];
	M[0] = dfa_replace_extrabit(M[0], M[1], "<img src=\"images/smile.gif\">",
			var, indices);
	dfaFree(freeM);
	//Block 2: if branch
	//M[3] is $message
	//$message = ereg_replace(">","&gt;",$message);
	dfaFree(M[1]);
	M[1] = dfa_construct_string(">", var, indices);
	M[3] = dfa_replace_extrabit(M[0], M[1], "&gt;", var, indices);

	//$message = ereg_replace("<","&lt;",$message);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("<", var, indices);
	freeM = M[3];
	M[3] = dfa_replace_extrabit(M[3], M[1], "&lt;", var, indices);
	dfaFree(freeM);

	//$message = ereg_replace("&lt;br&gt;","<br>",$message);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("&lt;br&gt;", var, indices);
	freeM = M[3];
	M[3] = dfa_replace_extrabit(M[3], M[1], "<br>", var, indices);
	dfaFree(freeM);

	//M[4] as $insert
	//$insert = "ASCII | <A href=\"$SCRIPT_NAME?id=$id&hardhtml=0\">HTML</a>";
	dfaFree(M[1]);
	M[1] = dfaSpecial6_2(var, indices); //$SCRIPT_NAME
	M[4] = dfa_construct_string("ASCII | <A href=\"", var, indices);
	M[4] = dfa_concat_extrabit(M[4], M[1], var, indices);
	M[4] = dfa_concat_extrabit(M[4], dfa_construct_string("?id=", var, indices),
			var, indices);
	M[4] = dfa_concat_extrabit(M[4], C[0], var, indices);
	M[4] = dfa_concat_extrabit(M[4],
			dfa_construct_string("&hardhtml=0\">HTML</a>", var, indices), var,
			indices);

	//Block 3: else branch
	//M[5] as $insert
	//$insert = "<a href=\"$SCRIPT_NAME?id=$id&hardhtml=1\">ASCII</a> | HTML";
	dfaFree(M[1]);
	M[1] = dfaSpecial6_2(var, indices); //$SCRIPT_NAME
	M[5] = dfa_construct_string("<a href=\"", var, indices);
	M[5] = dfa_concat_extrabit(M[5], M[1], var, indices);
	M[5] = dfa_concat_extrabit(M[5], dfa_construct_string("?id=", var, indices),
			var, indices);
	M[5] = dfa_concat_extrabit(M[5], C[0], var, indices);
	M[5] = dfa_concat_extrabit(M[5],
			dfa_construct_string("&hardhtml=1\">ASCII</a> | HTML", var,
					indices), var, indices);

	//Block 4: Union both branches
	//M[0] as $message
	//M[4] as $insert
	freeM = M[0];
	M[0] = dfaMinimize(dfaProduct(M[0], M[3], dfaOR));
	dfaFree(freeM);

	freeM = M[4];
	M[4] = dfaMinimize(dfaProduct(M[4], M[5], dfaOR));
	dfaFree(freeM);

	//M[2] as $name
	//$name = addslashes($_GET["name"]);
	dfaFree(M[2]);
	dfaFree(M[1]);
	//M[0] $row["title"] = addslashes($row["title"]);
	M[2] = dfaAllStringASCIIExceptReserveWords(var, indices);
	//function addslashes ($input)
	//$input = replace("'", "\\'", $input);

	M[1] = dfa_construct_string("'", var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "\\'", var, indices);
	//$input = replace("\"", "\\\"", $input);
	dfaFree(M[1]);
	M[1] = dfaChar('"', var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "\\\"", var, indices);
	//$input = replace("\\", "\\\\", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("\\", var, indices);
	M[2] = dfa_replace_extrabit(M[2], M[1], "\\\\", var, indices);

	//M[3] as $username
	//$username = addslashes($_GET["username"]);
	dfaFree(M[3]);
	dfaFree(M[1]);
	//M[0] $row["title"] = addslashes($row["title"]);
	M[3] = dfaAllStringASCIIExceptReserveWords(var, indices);
	//function addslashes ($input)
	//$input = replace("'", "\\'", $input);

	M[1] = dfa_construct_string("'", var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "\\'", var, indices);
	//$input = replace("\"", "\\\"", $input);
	dfaFree(M[1]);
	M[1] = dfaChar('"', var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "\\\"", var, indices);
	//$input = replace("\\", "\\\\", $input);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("\\", var, indices);
	M[3] = dfa_replace_extrabit(M[3], M[1], "\\\\", var, indices);

	//M[5] as $from
	//$from = "$name ($username)";
	dfaFree(M[5]);
	M[5] = dfa_concat_extrabit(M[2], dfa_construct_string(" (", var, indices),
			var, indices);
	M[5] = dfa_concat_extrabit(M[5], M[3], var, indices);
	M[5] = dfa_concat_extrabit(M[5], dfa_construct_string(")", var, indices),
			var, indices);

	dfaFree(M[1]);
	M[1] = dfa_construct_string(">", var, indices);
	freeM = M[5];
	M[5] = dfa_replace_extrabit(M[5], M[1], "&gt;", var, indices);
	dfaFree(freeM);

	//$message = ereg_replace("<","&lt;",$message);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("<", var, indices);
	freeM = M[5];
	M[5] = dfa_replace_extrabit(M[5], M[1], "&lt;", var, indices);
	dfaFree(freeM);

	//$message = ereg_replace("&lt;br&gt;","<br>",$message);
	dfaFree(M[1]);
	M[1] = dfa_construct_string("&lt;br&gt;", var, indices);
	freeM = M[5];
	M[5] = dfa_replace_extrabit(M[5], M[1], "<br>", var, indices);
	dfaFree(freeM);

	//M[2] as $content
	/*$content = "
	 <font face=\"Arial, Helvetica, Sans-serif\" size=2>
	 <div align=right><b>
	 <font face=\"Verdana, Helvetica, Sans-serif\" size=1>$insert</font>
	 </b></div>
	 <b>$strFrom:</b> $from<br><br>
	 <br>$message<br>";
	 */
	dfaFree(M[2]);
	M[2] =
			dfa_construct_string(
					"       <font face=\"Arial, Helvetica, Sans-serif\" size=2>\n       <div align=right><b>\n       <font face=\"Verdana, Helvetica, Sans-serif\" size=1>",
					var, indices);

	M[2] = dfa_concat_extrabit(M[2], M[4], var, indices); //M[4] is $insert
	M[2] = dfa_concat_extrabit(M[2],
			dfa_construct_string("</font>\n       </b></div>\n       <b>", var,
					indices), var, indices);
	M[2] = dfa_concat_extrabit(M[2], C[1], var, indices); //C[1] is $strFrom
	M[2] = dfa_concat_extrabit(M[2],
			dfa_construct_string(":</b> ", var, indices), var, indices);
	M[2] = dfa_concat_extrabit(M[2], M[5], var, indices); //M[5] is $from
	M[2] = dfa_concat_extrabit(M[2],
			dfa_construct_string("<br><br>\n       <br>", var, indices), var,
			indices);
	M[2] = dfa_concat_extrabit(M[2], M[0], var, indices); //M[0] is $message
	M[2] = dfa_concat_extrabit(M[2], dfa_construct_string("<br>", var, indices),
			var, indices);

	//echo default_font($content);
	/*
	 function default_font ($texto) {

	 $default_font_face = "Arial, Helvetica, Sans-serif";
	 $default_font_size = 2;

	 return  "<font face=\"$default_font_face\" size=$default_font_size>".
	 $texto.
	 "</font>";
	 }
	 */

	//$default_font_face = "Arial, Helvetica, Sans-serif";
	dfaFree(M[0]);
	M[0] = dfa_construct_string("Arial, Helvetica, Sans-serif", var, indices);
	//$default_font_size = 2;
	dfaFree(M[1]);
	M[1] = dfa_construct_string("2", var, indices);
	//M[3] as return value of
	dfaFree(M[3]);
	M[3] = dfa_construct_string("<font face=\"", var, indices);
	M[3] = dfa_concat_extrabit(M[3], M[0], var, indices); //M[0] is $default_font_face
	M[3] = dfa_concat_extrabit(M[3],
			dfa_construct_string(" size=", var, indices), var, indices);
	M[3] = dfa_concat_extrabit(M[3], M[1], var, indices); //M[1] is $default_font_size
	M[3] = dfa_concat_extrabit(M[3], dfa_construct_string(">", var, indices),
			var, indices);
	M[3] = dfa_concat_extrabit(M[3], M[2], var, indices); //M[2] is $texto
	M[3] = dfa_concat_extrabit(M[3],
			dfa_construct_string("</font>", var, indices), var, indices);

	//dfaPrintVitals(M[3]);

	i = check_intersection(M[3], tmpM, var, indices);
	if (i == 0)
		printf("Result: Secure!\n");
	else if (i == 1)
		printf("Result: Vulnerable!\n");
	else
		printf("Result: error in dfa_test_vul6() !\n");

#ifdef _COMPOSITE_ANALYSIS
	_a = construct_limit(M[3], var, indices); //limit constraint
#endif

	printf("Memory Allocated: %d\n", mem_allocated());

	for (j = 0; j < 6; j++) {
		//printf("Delete DFA %d\n", j);
		dfaFree(M[j]);
	}
	dfaFree(tmpM);
	dfaFree(C[0]);
	dfaFree(C[1]);
}
//end test

void dfa_test_pre_image(int var, int *indices) {
	DFA *tmp0 = NULL;
	DFA *tmp1 = NULL;
	DFA *tmp2 = NULL;
	DFA *tmp3 = NULL;
	DFA *tmp4 = NULL;

	tmp1 = dfa_closure_extrabit(dfa_construct_string("abcd", var, indices), var,
			indices);
	//tmp1=dfa_construct_string("abcd", var, indices);
	tmp2 = dfa_union(dfa_construct_string("ab", var, indices),
			dfa_construct_string("cd", var, indices));

	tmp3 = dfa_pre_concat_const(tmp1, "cd", 1, var, indices);

	printf("\n1. PreImange: M_(abcd)+ = X.cd\n");
	dfaPrintVerbose(tmp3);
	dfaFree(tmp3);
	tmp3 = dfa_pre_concat_const(tmp1, "ab", 2, var, indices);
	printf("\n2. PreImage: M_(abcd)+ = ab.X\n");
	dfaPrintVerbose(tmp3);
	dfaFree(tmp3);
	printf("\n3. PreImage: M_(abcd)+ = X.M_(ab|cd)\n");
	tmp3 = dfa_pre_concat(tmp1, tmp2, 1, var, indices);
	dfaPrintVerbose(tmp3);
	dfaFree(tmp3);
	printf("\n4. PreImage: M_(abcd)+ = M_(ab|cd).X\n");
	if (_FANG_DFA_DEBUG)
		dfaPrintVerbose(tmp2);
	tmp3 = dfa_pre_concat(tmp1, tmp2, 2, var, indices);
	dfaPrintVerbose(tmp3);
	dfaFree(tmp3);

	printf("\n5. General replace M_(abcd)+, M_(ab|cd), ab\n");
	tmp4 = dfa_construct_string("ab", var, indices);
	tmp3 = dfa_replace_extrabit(tmp1, tmp2, "ab", var, indices);
	printf("\nString replace");
	dfaPrintVerbose(tmp3);
	dfaFree(tmp3);
	printf("\nAutomata replace");
	tmp3 = dfa_general_replace_extrabit(tmp1, tmp2, tmp4, var, indices);
	tmp0 = tmp3;
	dfaPrintVerbose(tmp0);
	//dfaFree(tmp3);

	printf("\n6. PreImage of Replace M_(abcd)+, M_(ab|cd), M(ab)\n");
	tmp3 = dfa_pre_replace(tmp0, tmp2, tmp4, var, indices);
	dfaPrintVerbose(tmp3);
	dfaFree(tmp3);
	dfaFree(tmp0);

	printf("\n7. PreImage of Replace M_(abcd)+, M_(cd), " "\n");
	dfaFree(tmp4);
	tmp4 = dfa_construct_string("cd", var, indices);
	tmp0 = dfa_replace_extrabit(tmp1, tmp4, "", var, indices);
	printf("\n Replace result of Delete cd from (abcd)+:");
	dfaPrintVerbose(tmp0);
	tmp3 = dfa_pre_replace_str(tmp0, tmp4, "", var, indices);
	printf("\n Pre image of replace deletion:");
	dfaPrintVerbose(tmp3);
	dfaFree(tmp3);
	dfaFree(tmp0);

}

void dfa_test_multi_signature(int var, int *indices) {
	DFA *tmp0 = mdfaSignatureInput(0, 3, var, indices);
	DFA *tmp1 = mdfaSignatureInput(1, 3, var, indices);
	DFA *tmp2 = mdfaSignatureConstant(dfa_construct_string("ab", var, indices),
			3, var, indices);
	DFA *tmp = NULL;
	int* mindices = allocateMultipleAscIIIndex(3, var);
	int mvar = 3 * var;
	tmp = dfa_concat_extrabit(tmp0, tmp2, mvar, mindices);
	tmp = dfa_concat_extrabit(tmp, tmp1, mvar, mindices);
	dfaFree(tmp2);
	tmp2 = mdfaOneToManyTrackNoLambda(
			dfa_construct_string("cababc", var, indices), 3, 2, var, indices);
	tmp = dfa_intersect(tmp, tmp2);
	// dfaPrintVerbose(tmp);
	dfaFree(tmp0);
	tmp0 = dfaRemoveLastTrack(tmp, 3, var, indices);
	//dfaPrintVerbose(tmp0);
	mindices = allocateMultipleAscIIIndex(2, var);
	dfaPrintGraphviz(tmp0, 2 * var, mindices);
	dfaFree(tmp0);
	dfaFree(tmp1);
	dfaFree(tmp2);
	dfaFree(tmp);
}

void dfa_test_multi_signature_vul05(int var, int *indices) {
	DFA *i0 = mdfaSignatureInput(0, 3, var, indices);
	DFA *i1 = mdfaSignatureInput(1, 3, var, indices);
	DFA *c0 = mdfaSignatureConstant(
			dfa_construct_string("<tr>\n<td class=\"text\">", var, indices), 3,
			var, indices);
	DFA *c1 = mdfaSignatureConstant(
			dfa_construct_string("</td>\n<td class=\"text\">", var, indices), 3,
			var, indices);
	DFA *c2 = mdfaSignatureConstant(
			dfa_construct_string("</td>\n<td align=\"center\">\n", var,
					indices), 3, var, indices);
	int* mindices = allocateMultipleAscIIIndex(3, var);
	int mvar = 3 * var;

	DFA *m1 = dfa_concat_extrabit(c0, i0, mvar, mindices);
	DFA *m2 = dfa_concat_extrabit(m1, c1, mvar, mindices);
	DFA *m3 = dfa_concat_extrabit(m2, i1, mvar, mindices);
	DFA *m = dfa_concat_extrabit(m3, c2, mvar, mindices);
	//added for
	DFA *ma = NULL;
	DFA *ma1 = dfa_union(dfa_construct_string("S", var, indices),
			dfa_construct_string("s", var, indices));
	ma1 = dfa_concat_extrabit(dfa_construct_string("<", var, indices), ma1, var,
			indices);
	ma = dfa_concat_extrabit(dfaAllStringASCIIExceptReserveWords(var, indices),
			ma1, var, indices);
	ma = dfa_concat_extrabit(ma,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	//DFA *ma = dfa_concat_extrabit(dfaAllStringASCIIExceptReserveWords(var, indices), dfa_construct_string("<SCRIPT ", var, indices), var, indices);
	//ma = dfa_concat_extrabit(ma, dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

// ma is the attack pattern and we here extend the single track attack pattern automaton into multi track one using lambda
	ma = mdfaOneToManyTrackNoLambda(ma, 3, 2, var, indices);
	m = dfa_intersect(m, ma);
	m = dfaRemoveLastTrack(m, 3, var, indices);
	dfaPrintVitals(m);
	//mindices = allocateMultipleAscIIIndex(2, var);
	//m = dfaRemovePreLambda(m, getLambda(2*var), 2*var, mindices);
	//dfaPrintVitals(m);
	// m = dfaRemoveLambda(m, 2*var, mindices);
	//dfaPrintVerbose(m);
	mindices = allocateMultipleAscIIIndex(2, var);
	// when printing to dot we need to give var and indices for the number of tracks (m) -1 cause we already removed the output track
	dfaPrintGraphviz(m, 2 * var, mindices);
	printf("MONA memory:%d\n", mem_allocated());
	dfaFree(i0);
	dfaFree(i1);
	dfaFree(c0);
	dfaFree(c1);
	dfaFree(c2);
	dfaFree(m1);
	dfaFree(m2);
	dfaFree(m3);
	dfaFree(m);
}

void dfa_test_multi_signature_vul03(int var, int *indices) {
	DFA *i0 = mdfaSignatureInput(0, 4, var, indices);
	DFA *i1 = mdfaSignatureInput(1, 4, var, indices);
	DFA *i2 = mdfaSignatureInput(2, 4, var, indices);

	DFA *c0 = mdfaSignatureConstant(dfa_construct_string(" ", var, indices), 4,
			var, indices);
	DFA *c1 = mdfaSignatureConstant(
			dfa_construct_string("<FONT SIZE=1>", var, indices), 4, var,
			indices);
	DFA *c2 = mdfaSignatureConstant(
			dfa_construct_string("</FONT>", var, indices), 4, var, indices);
	int* mindices = allocateMultipleAscIIIndex(4, var);
	int mvar = 4 * var;
//dfaPrintVerbose(i0);
//dfaPrintVerbose(c0);

	DFA *m1 = dfa_concat_extrabit(i0, c0, mvar, mindices);
	DFA *m2 = dfa_concat_extrabit(c1, m1, mvar, mindices);
	DFA *m3 = dfa_concat_extrabit(i1, c0, mvar, mindices);
	DFA *m4 = dfa_concat_extrabit(m2, m3, mvar, mindices);
	DFA *m5 = dfa_concat_extrabit(i2, c0, mvar, mindices);
	DFA *m6 = dfa_concat_extrabit(m4, m5, mvar, mindices);

	DFA *m = dfa_concat_extrabit(m6, c2, mvar, mindices);
	DFA *ma = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<SCRIPT ", var, indices), var, indices);
	ma = dfa_concat_extrabit(ma,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	//dfaPrintVerbose(m1);

//  dfaPrintVitals(m4);
	//dfaPrintVitals(m6);
	//dfaPrintVerbose(m);

	ma = mdfaOneToManyTrackNoLambda(ma, 4, 3, var, indices);
	//dfaPrintVerbose(ma);

	m = dfa_intersect(m, ma);
	m = dfaRemoveLastTrack(m, 4, var, indices);
	mindices = allocateMultipleAscIIIndex(3, var);
	dfaPrintGraphviz(m, 3 * var, mindices);
	//  dfaPrintVitals(m);
	//mindices = allocateMultipleAscIIIndex(2, var);
	//m = dfaRemovePreLambda(m, getLambda(2*var), 2*var, mindices);
	//dfaPrintVitals(m);
	// m = dfaRemoveLambda(m, 2*var, mindices);
	//dfaPrintVerbose(m);
	printf("MONA memory:%d\n", mem_allocated());
	dfaFree(i0);
	dfaFree(i1);
	dfaFree(c0);
	dfaFree(c1);
	dfaFree(c2);
	dfaFree(m1);
	dfaFree(m2);
	dfaFree(m3);
	dfaFree(m);
}

void dfa_test_three_inputs_signature(int var, int *indices) {
	DFA *tmp0 = mdfaSignatureInput(0, 4, var, indices);
	DFA *tmp1 = mdfaSignatureInput(1, 4, var, indices);
	DFA *tmp2 = mdfaSignatureInput(2, 4, var, indices);

	DFA *tmp3 = mdfaSignatureConstant(dfa_construct_string("aaa", var, indices),
			4, var, indices);
	DFA *tmp = NULL;
	int* mindices = allocateMultipleAscIIIndex(4, var);
	int mvar = 4 * var;
	tmp = dfa_concat_extrabit(tmp3, tmp0, mvar, mindices);
	tmp = dfa_concat_extrabit(tmp, tmp1, mvar, mindices);
	tmp = dfa_concat_extrabit(tmp, tmp2, mvar, mindices); //please run mincut on tmp

	//dfaPrintGraphviz(tmp, 4*var, mindices); //output dot
	printf("before intersection\n");
	dfaPrintVerbose(tmp);

	DFA *ma = dfa_concat_extrabit(
			dfaAllStringASCIIExceptReserveWords(var, indices),
			dfa_construct_string("<SCRIPT ", var, indices), var, indices);
	ma = dfa_concat_extrabit(ma,
			dfaAllStringASCIIExceptReserveWords(var, indices), var, indices);

	ma = mdfaOneToManyTrackNoLambda(ma, 4, 3, var, indices);

	tmp = dfa_intersect(tmp, ma);
	printf("after intersection before remove output track\n");
	dfaPrintVerbose(tmp);
	tmp = dfaRemoveLastTrack(tmp, 4, var, indices);
	printf("after remove output track\n");
	dfaPrintVerbose(tmp);
	mindices = allocateMultipleAscIIIndex(3, var);
	dfaPrintGraphviz(tmp, 3 * var, mindices);

	printf("match input 1\n");
	char lambda = (char) 0xff;
	char * lambdaP = &lambda;

	DFA *t1 = dfaGetTrack(tmp, 0, 3, var, indices);
	t1 = dfaRemovePreLambda(t1, getLambda(var), var, indices);
	dfaPrintGraphviz(t1, var, indices);
	dfaPrintVerbose(t1);

	printf("match input 2\n");

	t1 = dfaGetTrack(tmp, 1, 3, var, indices);
	t1 = dfaRemovePreLambda(t1, getLambda(var), var, indices);
	dfaPrintGraphviz(t1, var, indices);
	dfaPrintVerbose(t1);
	printf("match input 3\n");

	t1 = dfaGetTrack(tmp, 2, 3, var, indices);
	t1 = dfaRemovePreLambda(t1, getLambda(var), var, indices);
	dfaPrintGraphviz(t1, var, indices);
	dfaPrintVerbose(t1);

	flush_output();

}
// for stranger option
unsigned dfaOption = 0;

// for output file name
FILE *out;

/*********************************************************************************************/
/**********************************  test function models   **********************************/
/*********************************************************************************************/

void testPreRightTrim() {
	int* indices_main = (int *) allocateAscIIIndexWithExtraBit(
			NUM_ASCII_TRACKS);
	int var = NUM_ASCII_TRACKS;
	dfaSetup(5, var, indices_main);

	//s0
	dfaAllocExceptions(1);
	dfaStoreException(1, "XXXXXXXX");
	dfaStoreState(4);

	//s1
	dfaAllocExceptions(1);
	dfaStoreException(2, "01100001"); //'a'
	dfaStoreState(4);

	//s2
	dfaAllocExceptions(1);
	dfaStoreException(3, "01100001"); //'a'
	dfaStoreState(4);

	//s3
	dfaAllocExceptions(1);
	dfaStoreException(2, "00100000"); //' '
	dfaStoreState(4);

	//s4 - sink
	dfaAllocExceptions(0);
	dfaStoreState(4);

	DFA* dfa = dfaBuild("000+-");

	printf("dfaSimpleBeforePreRightTrim:\n");
	//	dfaPrintGraphviz(dfa, var, indices_main);

	DFA* trimmed = dfaPreRightTrim(dfa, ' ', var, indices_main);
	printf("dfaSimpleAfterTrim:\n");
	//	dfaPrintGraphviz(trimmed, var, indices_main);
	dfaFree(dfa);
	dfa = NULL;
	dfaFree(trimmed);
	trimmed = NULL;

}

void testRightTrim() {
	/*
	 int* indices_main = (int *) allocateAscIIIndexWithExtraBit(NUM_ASCII_TRACKS);
	 int var = NUM_ASCII_TRACKS;
	 DFA* trimmedTest;

	 dfaSetup(5, var, indices_main);

	 //s0
	 dfaAllocExceptions(1);
	 dfaStoreException(1, "XXXXXXXX");
	 dfaStoreState(4);

	 //s1
	 dfaAllocExceptions(1);
	 dfaStoreException(2, "01100001");
	 dfaStoreState(4);

	 //s2
	 dfaAllocExceptions(1);
	 dfaStoreException(3, "00100000");
	 dfaStoreState(4);

	 //s3
	 dfaAllocExceptions(0);
	 dfaStoreState(4);

	 //s4 - sink
	 dfaAllocExceptions(0);
	 dfaStoreState(4);

	 DFA* dfa = dfaBuild("---+-");

	 printf("dfaSimpleBeforeTrim:\n");
	 dfaPrintGraphviz(dfa, var, indices_main);

	 DFA* trimmed = dfaRightTrim(dfa, ' ', var, indices_main);
	 printf("dfaSimpleAfterTrim:\n");
	 dfaPrintGraphviz(trimmed, var, indices_main);

	 dfaSetup(5, var, indices_main);

	 //s0
	 dfaAllocExceptions(1);
	 dfaStoreException(1, "XXXXXXXX");
	 dfaStoreState(3);

	 //s1
	 dfaAllocExceptions(1);
	 dfaStoreException(2, "01100001");
	 dfaStoreState(3);

	 //s2
	 dfaAllocExceptions(0);
	 dfaStoreState(3);

	 //s3 - sink
	 dfaAllocExceptions(0);
	 dfaStoreState(3);

	 trimmedTest = dfaBuild("--+-");

	 assert(check_equivalence(trimmed, trimmedTest, var, indices_main));
	 dfaFree(trimmedTest);
	 dfaFree(dfa);
	 dfaFree(trimmed);

	 dfaSetup(1, var, indices_main);
	 dfaAllocExceptions(0);
	 dfaStoreState(0);
	 DFA* empty = dfaBuild("-");
	 printf("dfaBeforeTrim:\n");
	 dfaPrintGraphviz(empty, var, indices_main);
	 trimmed = dfaRightTrim(empty, ' ', var, indices_main);
	 printf("dfaAfterTrim:\n");
	 dfaPrintGraphviz(trimmed, var, indices_main);
	 assert(check_equivalence(trimmed, empty, var, indices_main));
	 free(empty);
	 free(trimmed);
	 //
	 DFA* aSpaceb = dfa_construct_string("a b", var, indices_main);
	 printf("dfa_aSpaceb_BeforeTrim:\n");
	 dfaPrintGraphviz(aSpaceb, var, indices_main);
	 trimmed = dfaRightTrim(aSpaceb, ' ', var, indices_main);
	 printf("dfa_aSpaceb_AfterTrim:\n");
	 dfaPrintGraphviz(trimmed, var, indices_main);
	 assert(check_equivalence(trimmed, aSpaceb, var, indices_main));
	 dfaFree(aSpaceb);
	 dfaFree(trimmed);

	 DFA* abSpace = dfa_construct_string("ab ", var, indices_main);
	 printf("dfa_abSpace_BeforeTrim:\n");
	 dfaPrintGraphviz(abSpace, var, indices_main);
	 trimmed = dfaRightTrim(abSpace, ' ', var, indices_main);
	 printf("dfa_abSpace_AfterTrim:\n\n\n\n");
	 dfaPrintGraphviz(trimmed, var, indices_main);
	 DFA* ab = dfa_construct_string("ab", var, indices_main);
	 assert(check_equivalence(trimmed, ab, var, indices_main));
	 dfaFree(ab);
	 dfaFree(abSpace);
	 dfaFree(trimmed);

	 char* ltrA = bintostr('A', var);
	 char* ltrB = bintostr('B', var);
	 char* ltra = bintostr('a', var);
	 char* ltrb = bintostr('b', var);
	 char* ltrz = bintostr('z', var);
	 char* ltrSpace = bintostr(' ', var);

	 dfaSetup(9, var, indices_main);

	 //s0
	 dfaAllocExceptions(5);
	 dfaStoreException(1, ltrA);
	 dfaStoreException(1, ltrb);
	 dfaStoreException(1, ltrz);
	 dfaStoreException(1, ltrSpace);
	 dfaStoreException(1, ltra);
	 dfaStoreState(8);

	 //s1
	 dfaAllocExceptions(4);
	 dfaStoreException(2, ltrA);
	 dfaStoreException(2, ltrb);
	 dfaStoreException(2, ltrz);
	 dfaStoreException(2, ltra);
	 dfaStoreState(8);

	 //s2
	 dfaAllocExceptions(5);
	 dfaStoreException(3, ltrA);
	 dfaStoreException(3, ltrb);
	 dfaStoreException(3, ltrz);
	 dfaStoreException(3, ltrSpace);
	 dfaStoreException(3, ltrB);
	 dfaStoreState(8);

	 //s3
	 dfaAllocExceptions(3);
	 dfaStoreException(4, ltrA);
	 dfaStoreException(4, ltrSpace);
	 dfaStoreException(4, ltra);
	 dfaStoreState(8);

	 //s4
	 dfaAllocExceptions(1);
	 dfaStoreException(5, ltrSpace);
	 dfaStoreState(8);

	 //s5
	 dfaAllocExceptions(2);
	 dfaStoreException(6, ltrb);
	 dfaStoreException(6, ltrSpace);
	 dfaStoreState(8);

	 //s6
	 dfaAllocExceptions(4);
	 dfaStoreException(7, ltrA);
	 dfaStoreException(7, ltrb);
	 dfaStoreException(7, ltrz);
	 dfaStoreException(7, ltrSpace);
	 dfaStoreState(8);

	 //s7 -- accept
	 dfaAllocExceptions(0);
	 dfaStoreState(8);

	 //s8 - sink
	 dfaAllocExceptions(0);
	 dfaStoreState(8);

	 DFA* complex = dfaBuild("-------+-");
	 printf("dfa_Complex1_BeforeTrim:\n");
	 dfaPrintGraphviz(complex, var, indices_main);
	 trimmed = dfaRightTrim(complex, ' ', var, indices_main);
	 printf("dfa_Complex1_AfterTrim:\n\n\n\n");
	 dfaPrintGraphviz(trimmed, var, indices_main);
	 dfaFree(complex);
	 dfaFree(trimmed);

	 dfaSetup(11, var, indices_main);

	 //s0
	 dfaAllocExceptions(1);
	 dfaStoreException(1, ltra);
	 dfaStoreState(10);

	 //s1
	 dfaAllocExceptions(2);
	 dfaStoreException(2, ltrb);
	 dfaStoreException(7, ltrSpace);
	 dfaStoreState(10);

	 //s2
	 dfaAllocExceptions(3);
	 dfaStoreException(3, ltra);
	 dfaStoreException(3, ltrSpace);
	 dfaStoreException(6, ltrb);
	 dfaStoreState(10);

	 //s3
	 dfaAllocExceptions(2);
	 dfaStoreException(4, ltra);
	 dfaStoreException(4, ltrSpace);
	 dfaStoreState(10);

	 //s4
	 dfaAllocExceptions(2);
	 dfaStoreException(3, ltra);
	 dfaStoreException(5, ltrSpace);
	 dfaStoreState(10);

	 //s5 - accept state 1
	 dfaAllocExceptions(0);
	 dfaStoreState(10);

	 //s6
	 dfaAllocExceptions(2);
	 dfaStoreException(7, ltrb);
	 dfaStoreException(4, ltrSpace);
	 dfaStoreState(10);

	 //s7
	 dfaAllocExceptions(2);
	 dfaStoreException(8, ltrSpace);
	 dfaStoreException(9, ltrb);
	 dfaStoreState(10);

	 //s8 - accept state 2
	 dfaAllocExceptions(2);
	 dfaStoreException(7, ltrSpace);
	 dfaStoreException(7, ltrb);
	 dfaStoreState(10);

	 //s9 - accept state 3
	 dfaAllocExceptions(0);
	 dfaStoreState(10);

	 //s10 - sink
	 dfaAllocExceptions(0);
	 dfaStoreState(10);


	 complex = dfaBuild("00000+00++-");
	 printf("dfa_Complex2_BeforeTrim:\n");
	 dfaPrintGraphviz(complex, var, indices_main);
	 trimmed = dfaRightTrim(complex, ' ', var, indices_main);
	 printf("dfa_Complex2_AfterTrim:\n\n\n\n");
	 dfaPrintGraphviz(trimmed, var, indices_main);
	 dfaFree(complex);
	 dfaFree(trimmed);

	 dfaSetup(15, var, indices_main);

	 //s0
	 dfaAllocExceptions(3);
	 dfaStoreException(1, ltrb);
	 dfaStoreException(1, ltrSpace);
	 dfaStoreException(6, ltra);
	 dfaStoreState(14);

	 //s1
	 dfaAllocExceptions(3);
	 dfaStoreException(2, ltrb);
	 dfaStoreException(2, ltrSpace);
	 dfaStoreException(3, ltra);
	 dfaStoreState(14);

	 //s2
	 dfaAllocExceptions(2);
	 dfaStoreException(4, ltra);
	 dfaStoreException(4, ltrSpace);
	 dfaStoreState(14);

	 //s3
	 dfaAllocExceptions(2);
	 dfaStoreException(4, ltra);
	 dfaStoreException(4, ltrSpace);
	 dfaStoreState(14);

	 //s4
	 dfaAllocExceptions(2);
	 dfaStoreException(5, ltra);
	 dfaStoreException(5, ltrSpace);
	 dfaStoreState(14);

	 //s5 - accept state 1
	 dfaAllocExceptions(2);
	 dfaStoreException(5, ltrSpace);
	 dfaStoreException(2, ltra);
	 dfaStoreState(14);

	 //s6
	 dfaAllocExceptions(3);
	 dfaStoreException(11, ltrb);
	 dfaStoreException(7, ltrz);
	 dfaStoreException(9, ltra);
	 dfaStoreState(14);

	 //s7
	 dfaAllocExceptions(2);
	 dfaStoreException(8, ltrSpace);
	 dfaStoreException(8, ltra);
	 dfaStoreState(14);

	 //s8
	 dfaAllocExceptions(2);
	 dfaStoreException(5, ltrSpace);
	 dfaStoreException(5, ltra);
	 dfaStoreState(14);

	 //s9
	 dfaAllocExceptions(2);
	 dfaStoreException(10, ltrSpace);
	 dfaStoreException(10, ltrb);
	 dfaStoreState(14);

	 //s10
	 dfaAllocExceptions(2);
	 dfaStoreException(13, ltrSpace);
	 dfaStoreException(9, ltra);
	 dfaStoreState(14);

	 //s11
	 dfaAllocExceptions(2);
	 dfaStoreException(9, ltra);
	 dfaStoreException(12, ltrb);
	 dfaStoreState(14);

	 //s12
	 dfaAllocExceptions(2);
	 dfaStoreException(10, ltrSpace);
	 dfaStoreException(10, ltra);
	 dfaStoreState(14);

	 //s13 - accept satate 2
	 dfaAllocExceptions(1);
	 dfaStoreException(5, ltrSpace);
	 dfaStoreState(14);

	 //s14 - sink
	 dfaAllocExceptions(0);
	 dfaStoreState(14);


	 complex = dfaBuild("00000+0000000+-");
	 printf("dfa_Complex3_BeforeTrim:\n");
	 dfaPrintGraphviz(complex, var, indices_main);
	 trimmed = dfaRightTrim(complex, ' ', var, indices_main);
	 printf("dfa_Complex3_AfterTrim:\n\n\n\n");
	 dfaPrintGraphviz(trimmed, var, indices_main);
	 DFA* fourS = dfa_construct_string("    ", var, indices_main);
	 assert(!check_intersection(trimmed, fourS, var, indices_main));
	 DFA* bfourS = dfa_construct_string("b    ", var, indices_main);
	 assert(!check_intersection(trimmed, bfourS, var, indices_main));
	 DFA* azaS = dfa_construct_string("aza ", var, indices_main);
	 assert(!check_intersection(trimmed, azaS, var, indices_main));
	 DFA* a = dfa_construct_string("a", var, indices_main);
	 assert(!check_intersection(trimmed, a, var, indices_main));
	 ab = dfa_construct_string("ab", var, indices_main);
	 assert(!check_intersection(trimmed, ab, var, indices_main));
	 DFA* aa = dfa_construct_string("aa", var, indices_main);
	 assert(check_intersection(trimmed, aa, var, indices_main));
	 DFA* Sa = dfa_construct_string("   a", var, indices_main);
	 assert(check_intersection(trimmed, Sa, var, indices_main));
	 DFA* SaSa = dfa_construct_string(" a a", var, indices_main);
	 assert(check_intersection(trimmed, SaSa, var, indices_main));
	 DFA* abbSSSSSaaa = dfa_construct_string("abb     aaa", var, indices_main);
	 assert(check_intersection(trimmed, abbSSSSSaaa, var, indices_main));
	 dfaFree(bfourS);
	 dfaFree(azaS);
	 dfaFree(a);
	 dfaFree(ab);
	 dfaFree(aa);
	 dfaFree(Sa);
	 dfaFree(SaSa);
	 dfaFree(abbSSSSSaaa);
	 dfaFree(fourS);
	 dfaFree(complex);
	 dfaFree(trimmed);

	 //we need more test


	 free(ltrA);
	 free(ltrB);
	 free(ltra);
	 free(ltrb);
	 free(ltrz);
	 free(ltrSpace);
	 */
}

void testToLowerUpperCaseHelper(boolean lowerCase) {
	/*
	 int var = NUM_ASCII_TRACKS;
	 int* indices = (int *) allocateAscIIIndexWithExtraBit(NUM_ASCII_TRACKS);
	 int i;
	 char* symbol;
	 DFA* dfa, *dfa2, *result, *tmp;

	 printf("test dfaToLowerUpperCase();\n\n\n");

	 //	// test empty language
	 //	dfa = dfaASCIINonString(var, indices);
	 //	result = dfaToLowerCase(dfa, var, indices);
	 //	dfaPrintGraphviz(result, var, indices);
	 //	assert(check_equivalence(dfa, result, var, indices));
	 //	dfaFree(dfa); dfa = NULL;
	 //	dfaFree(result); result = NULL;
	 //
	 //	printf("1st passed\n\n\n");
	 //
	 //	// test language with empty string only
	 //	dfa = dfaASCIIOnlyNullString(var, indices);
	 //	result = dfaToLowerCase(dfa, var, indices);
	 //	dfaPrintGraphviz(dfa, var, indices);
	 //	dfaPrintGraphviz(result, var, indices);
	 //	assert(check_equivalence(dfa, result, var, indices));
	 //	dfaFree(dfa); dfa = NULL;
	 //	dfaFree(result); result = NULL;
	 //
	 //	printf("2nd passed\n\n\n");

	 // accepts a length of one charachter
	 dfaSetup(3, var, indices);
	 //s0
	 dfaAllocExceptions(0);
	 dfaStoreState(1);
	 //s1
	 dfaAllocExceptions(0);
	 dfaStoreState(2);
	 //s2
	 dfaAllocExceptions(0);
	 dfaStoreState(2);
	 dfa = dfaBuild("0+-");
	 dfaPrintGraphviz(dfa, var, indices);

	 // accepts a length of one charachter that is not capital letter
	 dfaSetup(3, var, indices);
	 //s0
	 dfaAllocExceptions(230);
	 int first, last;
	 if (lowerCase){
	 first = 65;last = 90;
	 }
	 else{
	 first = 97; last = 122;
	 }
	 for (i = 0; i < 256; i++){

	 if (i < first || i > last){
	 symbol = bintostr(i, var);
	 dfaStoreException(1, symbol);
	 free(symbol); symbol = NULL;
	 }
	 }
	 dfaStoreState(2);
	 //s1
	 dfaAllocExceptions(0);
	 dfaStoreState(2);
	 //s2
	 dfaAllocExceptions(0);
	 dfaStoreState(2);
	 tmp = dfaBuild("0+-");
	 dfaPrintGraphviz(tmp, var, indices);

	 result = lowerCase? dfaToLowerCase(dfa, var, indices): dfaToUpperCase(dfa, var, indices);;
	 dfaPrintGraphviz(result, var, indices);
	 assert(check_equivalence(tmp, result, var, indices));
	 dfaFree(dfa); dfa = NULL;
	 dfaFree(result); result = NULL;
	 dfaFree(tmp); tmp = NULL;
	 printf("3rd passed\n\n\n");



	 dfa = lowerCase? dfa_construct_string("?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`a", var, indices): dfa_construct_string("_`abcdefghijklmnopqrstuvwxyz{}|~A", var, indices);;
	 dfaPrintGraphviz(dfa, var, indices);
	 result = lowerCase? dfaToLowerCase(dfa, var, indices) : dfaToUpperCase(dfa, var, indices);
	 dfaFree(dfa); dfa = NULL;
	 dfa = lowerCase? dfa_construct_string("?@abcdefghijklmnopqrstuvwxyz[\\]^_`a", var, indices) : dfa_construct_string("_`ABCDEFGHIJKLMNOPQRSTUVWXYZ{}|~A", var, indices);
	 dfaPrintGraphviz(dfa, var, indices);
	 dfaPrintGraphviz(result, var, indices);
	 assert(check_equivalence(dfa, result, var, indices));
	 dfaFree(dfa); dfa = NULL;
	 dfaFree(result); result = NULL;
	 printf("4th passed\n\n\n");


	 char* alphaC = lowerCase? "?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`a": "_`abcdefghijklmnopqrstuvwxyz{}|~A";
	 char* alphaS = lowerCase? "?@abcdefghijklmnopqrstuvwxyz[\\]^_`a": "_`ABCDEFGHIJKLMNOPQRSTUVWXYZ{}|~A";
	 char** set = (char**) malloc((strlen(alphaC)) * sizeof(char*));
	 for(i = 0; i < strlen(alphaC); i++){
	 set[i] = (char*) malloc(2 * sizeof(char));
	 set[i][0] = alphaC[i]; set[i][1] = '\0';
	 printf("%s, ", set[i]);
	 }
	 printf("\n");
	 char** set2 = (char**) malloc((strlen(alphaS)) * sizeof(char*));
	 for(i = 0; i < strlen(alphaS); i++){
	 set2[i] = (char*) malloc(2 * sizeof(char));
	 set2[i][0] = alphaS[i]; set2[i][1] = '\0';
	 printf("%s, ", set2[i]);
	 }
	 printf("\n");
	 dfa = dfa_construct_set_of_strings(set, strlen(alphaC), var, indices);
	 dfaPrintGraphviz(dfa, var, indices);
	 dfa2 = dfa_construct_set_of_strings(set2, strlen(alphaS), var, indices);
	 dfaPrintGraphviz(dfa2, var, indices);
	 result = lowerCase? dfaToLowerCase(dfa, var, indices) : dfaToUpperCase(dfa, var, indices);
	 dfaPrintGraphviz(result, var, indices);
	 assert(check_equivalence(dfa2, result, var, indices));
	 dfaFree(dfa);dfa = NULL;
	 dfaFree(dfa2);dfa2 = NULL;
	 dfaFree(result);result = NULL;
	 for (i = 0; i < strlen(alphaC); i++)
	 free(set[i]);
	 free(set);set = NULL;
	 for (i = 0; i < strlen(alphaS); i++)
	 free(set2[i]);
	 free(set2); set2 = NULL;
	 printf("5th passed\n\n\n");


	 alphaC = lowerCase? "()*+01,-./?@ABDEFHIJKLMNOPQRSTUVWXYZ[\\]^_`a" : "()*+01,-./?@abdefhijklmnopqrstuvwxyz{}|~A";
	 alphaS = lowerCase? "()*+01,-./?@abdefhijklmnopqrstuvwxyz[\\]^_`a" : "()*+01,-./?@ABDEFHIJKLMNOPQRSTUVWXYZ{}|~A";
	 set = (char**) malloc((strlen(alphaC)) * sizeof(char*));
	 for(i = 0; i < strlen(alphaC); i++){
	 set[i] = (char*) malloc(2 * sizeof(char));
	 set[i][0] = alphaC[i]; set[i][1] = '\0';
	 printf("%s, ", set[i]);
	 }
	 printf("\n");
	 set2 = (char**) malloc((strlen(alphaS)) * sizeof(char*));
	 for(i = 0; i < strlen(alphaS); i++){
	 set2[i] = (char*) malloc(2 * sizeof(char));
	 set2[i][0] = alphaS[i]; set2[i][1] = '\0';
	 printf("%s, ", set2[i]);
	 }
	 printf("\n");
	 dfa = dfa_construct_set_of_strings(set, strlen(alphaC), var, indices);
	 dfaPrintGraphviz(dfa, var, indices);
	 dfa2 = dfa_construct_set_of_strings(set2, strlen(alphaS), var, indices);
	 dfaPrintGraphviz(dfa2, var, indices);
	 result = lowerCase? dfaToLowerCase(dfa, var, indices) : dfaToUpperCase(dfa, var, indices);
	 dfaPrintGraphviz(result, var, indices);
	 assert(check_equivalence(dfa2, result, var, indices));
	 dfaFree(dfa);dfa = NULL;
	 dfaFree(dfa2);dfa2 = NULL;
	 dfaFree(result);result = NULL;
	 for (i = 0; i < strlen(alphaC); i++)
	 free(set[i]);
	 free(set);set = NULL;
	 for (i = 0; i < strlen(alphaS); i++)
	 free(set2[i]);
	 free(set2); set2 = NULL;
	 printf("6th passed\n\n\n");


	 alphaC = lowerCase? " 0@P!1AQ" : " 0\"2`pbr";
	 alphaS = lowerCase? " 0@p!1aq" : " 0\"2`PBR";
	 set = (char**) malloc((strlen(alphaC)) * sizeof(char*));
	 for(i = 0; i < strlen(alphaC); i++){
	 set[i] = (char*) malloc(2 * sizeof(char));
	 set[i][0] = alphaC[i]; set[i][1] = '\0';
	 printf("%s, ", set[i]);
	 }
	 printf("\n");
	 set2 = (char**) malloc((strlen(alphaS)) * sizeof(char*));
	 for(i = 0; i < strlen(alphaS); i++){
	 set2[i] = (char*) malloc(2 * sizeof(char));
	 set2[i][0] = alphaS[i]; set2[i][1] = '\0';
	 printf("%s, ", set2[i]);
	 }
	 printf("\n");
	 dfa = dfa_construct_set_of_strings(set, strlen(alphaC), var, indices);
	 dfaPrintGraphviz(dfa, var, indices);
	 dfa2 = dfa_construct_set_of_strings(set2, strlen(alphaS), var, indices);
	 dfaPrintGraphviz(dfa2, var, indices);
	 result = lowerCase? dfaToLowerCase(dfa, var, indices) : dfaToUpperCase(dfa, var, indices);
	 dfaPrintGraphviz(result, var, indices);
	 assert(check_equivalence(dfa2, result, var, indices));
	 dfaFree(dfa);dfa = NULL;
	 dfaFree(dfa2);dfa2 = NULL;
	 dfaFree(result);result = NULL;
	 for (i = 0; i < strlen(alphaC); i++)
	 free(set[i]);
	 free(set);set = NULL;
	 for (i = 0; i < strlen(alphaS); i++)
	 free(set2[i]);
	 free(set2); set2 = NULL;
	 printf("7th passed\n\n\n");
	 */
}

void testToLowerUpperCase() {
	testToLowerUpperCaseHelper(TRUE);
	testToLowerUpperCaseHelper(FALSE);
}

void testLeftTrim() {
	/*
	 int* indices_main = (int *) allocateAscIIIndexWithExtraBit(NUM_ASCII_TRACKS);
	 int var = NUM_ASCII_TRACKS;
	 int i, j, k;
	 char* trimmeds;
	 DFA* trimmed, *dfaString;


	 printf("running testLeftTrim()\n\n");

	 dfaSetup(5, var, indices_main);

	 //s0
	 dfaAllocExceptions(1);
	 dfaStoreException(1, "XXXXXXXX");
	 dfaStoreState(4);

	 //s1
	 dfaAllocExceptions(1);
	 dfaStoreException(2, "00100000");
	 dfaStoreState(4);

	 //s2
	 dfaAllocExceptions(1);
	 dfaStoreException(3, "01100001");
	 dfaStoreState(4);

	 //s3
	 dfaAllocExceptions(0);
	 dfaStoreState(4);

	 //s4 - sink
	 dfaAllocExceptions(0);
	 dfaStoreState(4);

	 DFA* dfa = dfaBuild("000+-");

	 printf("dfaBeforeTrim:\n");
	 dfaPrintGraphviz(dfa, var, indices_main);

	 trimmed = dfaLeftTrim(dfa, ' ', var, indices_main);
	 printf("dfaAfterTrim:\n");
	 dfaPrintGraphviz(trimmed, var, indices_main);
	 dfaFree(dfa);
	 dfaFree(trimmed);

	 printf("test1 passed\n\n\n");

	 dfaSetup(1, var, indices_main);
	 dfaAllocExceptions(0);
	 dfaStoreState(0);
	 DFA* empty = dfaBuild("-");
	 printf("dfaBeforeTrim:\n");
	 dfaPrintGraphviz(empty, var, indices_main);
	 trimmed = dfaLeftTrim(empty, ' ', var, indices_main);
	 printf("dfaAfterTrim:\n");
	 dfaPrintGraphviz(trimmed, var, indices_main);
	 dfaFree(empty);
	 dfaFree(trimmed);

	 printf("test2 passed\n\n\n");


	 DFA* aSpaceb = dfa_construct_string("a b", var, indices_main);
	 printf("dfaBeforeTrim:\n");
	 dfaPrintGraphviz(aSpaceb, var, indices_main);
	 trimmed = dfaLeftTrim(aSpaceb, "00100000", var, indices_main);
	 printf("dfaAfterTrim:\n");
	 dfaPrintGraphviz(trimmed, var, indices_main);
	 assert(check_equivalence(aSpaceb, trimmed, var, indices_main));
	 dfaFree(aSpaceb);
	 dfaFree(trimmed);

	 printf("test3 passed\n\n\n");


	 char** chars = (char**)malloc(256 * sizeof(char*));
	 for (i = 0; i < 256; i++){
	 chars[i] = bintostr((char)i, var);
	 }

	 dfaSetup(9, var, indices_main);

	 //s0
	 dfaAllocExceptions(2);
	 dfaStoreException(1, "X0X0X0X0");
	 dfaStoreException(6, chars['a']);
	 dfaStoreState(8);

	 //s1
	 dfaAllocExceptions(2);
	 dfaStoreException(2, "XX10XX00");
	 dfaStoreException(0, chars['a']);
	 dfaStoreState(8);

	 //s2
	 dfaAllocExceptions(2);
	 dfaStoreException(3, "XXX0XXX0");
	 dfaStoreException(1, chars['A']);
	 dfaStoreState(8);

	 //s3
	 dfaAllocExceptions(3);
	 dfaStoreException(1, chars['A']);
	 dfaStoreException(0, "0010XXXX");
	 dfaStoreException(4, chars['a']);
	 dfaStoreState(8);

	 //s4
	 dfaAllocExceptions(1);
	 dfaStoreException(5, chars['b']);
	 dfaStoreState(8);

	 //s5
	 dfaAllocExceptions(1);
	 dfaStoreException(0, chars['b']);
	 dfaStoreState(8);

	 //s6
	 dfaAllocExceptions(2);
	 dfaStoreException(7, chars['b']);
	 dfaStoreException(7, chars[' ']);
	 dfaStoreState(8);

	 //s7
	 dfaAllocExceptions(1);
	 dfaStoreException(0, chars['z']);
	 dfaStoreState(8);

	 //s8 - sink
	 dfaAllocExceptions(0);
	 dfaStoreState(8);

	 DFA* complex = dfaBuild("-----+---");
	 printf("dfaBeforeTrim:\n");
	 dfaPrintGraphviz(complex, var, indices_main);

	 char* testStringsBase[] = {"*,J#   ab", "(lb+   ab", "\"d@    ab", "* n-   ab", "* n    ab", "(  %   ab", "(      ab", "*l     ab", "*l )   ab",
	 "*,J#*  ab", "(lb+ l ab", "\"d@   @ab", "* n-   ab", "* n    ab", "(  %   ab", "(      ab", "*l     ab", "*l )   ab",
	 "*lJab"    , "(lbab"    , "\"d@ab"    , "* nab"    ,              "(  ab"    , "(  ab"    , "*l ab"                  };
	 int size = 25;
	 for (i = 0; i < size; i++){
	 printf("%s\n", testStringsBase[i]);
	 flush_output();
	 dfaString = dfa_construct_string(testStringsBase[i], var, indices_main);
	 assert(check_inclusion(dfaString, complex, var, indices_main));
	 dfaFree(dfaString);
	 assert(checkMembership(complex, testStringsBase[i], var, indices_main));
	 }
	 printf("\n");

	 char** testStrings1 = (char**) malloc(size * sizeof(char*));
	 for (j = 0; j < 3; j++ ){
	 printf("\n\nnumber of spaces is %d\n\n", (j+1));
	 for (i = 0; i < size; i++){
	 testStrings1[i] = (char*) malloc( ( strlen( testStringsBase[i] ) + 1) * sizeof(char));
	 strcpy(testStrings1[i], testStringsBase[i]);
	 for(k = 0; k <= j; k++)
	 testStrings1[i][k] = ' ';
	 printf("%s\n", testStrings1[i]);
	 flush_output();
	 dfaString = dfa_construct_string(testStrings1[i], var, indices_main);
	 assert(check_inclusion(dfaString, complex, var, indices_main));
	 dfaFree(dfaString);
	 assert(checkMembership(complex, testStrings1[i], var, indices_main));
	 free(testStrings1[i]);
	 }
	 }
	 free(testStrings1);


	 trimmed = dfaLeftTrim(complex, ' ', var, indices_main);
	 printf("dfaAfterTrim:\n");
	 dfaPrintGraphviz(trimmed, var, indices_main);

	 for (i = 0; i < size; i++){
	 printf("%s\n", testStringsBase[i]);
	 flush_output();
	 dfaString = dfa_construct_string(testStringsBase[i], var, indices_main);
	 assert(check_inclusion(dfaString, trimmed, var, indices_main));
	 dfaFree(dfa_construct_string(testStringsBase[i], var, indices_main));
	 assert(checkMembership(trimmed, testStringsBase[i], var, indices_main));
	 }
	 printf("\n");

	 testStrings1 = (char**) malloc(size * sizeof(char*));
	 for (j = 0; j < 3; j++ ){
	 printf("\n\nnumber of spaces is %d\n\n", (j+1));
	 for (i = 0; i < size; i++){
	 testStrings1[i] = (char*) malloc( ( strlen( testStringsBase[i] ) + 1) * sizeof(char));
	 strcpy(testStrings1[i], testStringsBase[i]);
	 for(k = 0; k <= j; k++)
	 testStrings1[i][k] = ' ';
	 printf("%s\t\t--\t\t", testStrings1[i]);
	 flush_output();
	 dfaString = dfa_construct_string(testStrings1[i], var, indices_main);
	 assert(!check_inclusion(dfaString, trimmed, var, indices_main));
	 dfaFree(dfaString);
	 assert(!checkMembership(trimmed, testStrings1[i], var, indices_main));
	 trimmeds = (char*) malloc( (strlen(testStrings1[i]) + 1) * sizeof(char) );
	 trimwhitespace(trimmeds, strlen(testStrings1[i])+1, testStrings1[i]);
	 printf("%s\n", trimmeds);
	 flush_output();
	 dfaString = dfa_construct_string(trimmeds, var, indices_main);
	 assert(check_inclusion(dfaString, trimmed, var, indices_main));
	 dfaFree(dfaString);
	 assert(checkMembership(trimmed, trimmeds, var, indices_main));
	 free(trimmeds);
	 free(testStrings1[i]);
	 }
	 }
	 free(testStrings1);

	 dfaFree(complex);
	 dfaFree(trimmed);

	 for (i = 0; i < 256; i++)
	 free(chars[i]);
	 free(chars);
	 */

}

DFA *test_project(DFA *M, int var, int *oldindices, int len, int fast) {
	DFA *result = NULL;
	paths state_paths, pp;
	trace_descr tp;

	int i, j, k;

	char *exeps;
	int *to_states;
	long max_exeps;
	char *statuces;
	int sink;

	char *symbol;

	int *indices = allocateArbitraryIndex(len); //indices is updated if you need to add auxiliary bits

	symbol = (char *) malloc((var + 1) * sizeof(char));

	max_exeps = 1 << len; //maybe exponential
	sink = find_sink(M);
	assert(sink > -1);

	dfaSetup(M->ns, len, indices); //add one new accept state
	exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char)); //plus 1 for \0 end of the string
	to_states = (int *) malloc(max_exeps * sizeof(int));
	statuces = (char *) malloc((M->ns + 1) * sizeof(char)); //plus 2, one for the new accept state and one for \0 end of the string

	// for each original state
	for (i = 0; i < M->ns; i++) {
		state_paths = pp = make_paths(M->bddm, M->q[i]);
		k = 0;
		// for each transition out from current state (state i)
		while (pp) {
			if (pp->to != sink) {
				for (j = 0; j < var; j++) {
					//the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != indices[j]); tp =
							tp->next)
						;

					if (tp) {
						if (tp->value)
							symbol[j] = '1';
						else
							symbol[j] = '0';
					} else
						symbol[j] = 'X';
				}
				symbol[var] = '\0';

				to_states[k] = pp->to; // destination new accept state
				for (j = 0; j < var; j++)
					exeps[k * (len + 1) + j] = symbol[j];
				for (j = var; j < len; j++)
					exeps[k * (len + 1) + j] = '0';
				exeps[k * (len + 1) + len] = '\0';
				k++;

				if (fast) {
					int i1, i2, i3, i4, i5, i6, i7, i8;
					for (i1 = 0; i1 < 2; i1++)
						for (i2 = 0; i2 < 2; i2++)
							for (i3 = 0; i3 < 2; i3++)
								for (i4 = 0; i4 < 2; i4++)
									for (i5 = 0; i5 < 2; i5++)
										for (i6 = 0; i6 < 2; i6++)
											for (i7 = 0; i7 < 2; i7++)
												for (i8 = 0; i8 < 2; i8++) {
													to_states[k] = pp->to; // destination new accept state
													for (j = 0; j < var; j++)
														exeps[k * (len + 1) + j] =
																symbol[j];
													if (i1 == 0)
														exeps[k * (len + 1)
																+ var] = '0';
													else
														exeps[k * (len + 1)
																+ var] = '1';
													if (i2 == 0)
														exeps[k * (len + 1)
																+ var + 1] =
																'0';
													else
														exeps[k * (len + 1)
																+ var + 1] =
																'1';
													if (i3 == 0)
														exeps[k * (len + 1)
																+ var + 2] =
																'0';
													else
														exeps[k * (len + 1)
																+ var + 2] =
																'1';
													if (i4 == 0)
														exeps[k * (len + 1)
																+ var + 3] =
																'0';
													else
														exeps[k * (len + 1)
																+ var + 3] =
																'1';
													if (i5 == 0)
														exeps[k * (len + 1)
																+ var + 4] =
																'0';
													else
														exeps[k * (len + 1)
																+ var + 4] =
																'1';
													if (i6 == 0)
														exeps[k * (len + 1)
																+ var + 5] =
																'0';
													else
														exeps[k * (len + 1)
																+ var + 5] =
																'1';
													if (i7 == 0)
														exeps[k * (len + 1)
																+ var + 6] =
																'0';
													else
														exeps[k * (len + 1)
																+ var + 6] =
																'1';
													if (i8 == 0)
														exeps[k * (len + 1)
																+ var + 7] =
																'0';
													else
														exeps[k * (len + 1)
																+ var + 7] =
																'1';
													exeps[k * (len + 1) + len] =
															'\0';
													k++;
												}
				}
			}
			pp = pp->next;
		} //end while

		dfaAllocExceptions(k);
		for (k--; k >= 0; k--)
			dfaStoreException(to_states[k], exeps + k * (len + 1));
		dfaStoreState(sink);
		if (M->f[i] == 1)
			statuces[i] = '+';
		else
			statuces[i] = '-';

		kill_paths(state_paths);
	} // end for each original state
	  //    assert(new_state_counter == (num_new_states - 1));
	statuces[M->ns] = '\0';
	result = dfaBuild(statuces);

	for (j = var; j < len; j++) {
		DFA *tmp = dfaProject(result, j);
		dfaFree(result);
		result = dfaMinimize(tmp);
		dfaFree(tmp);
	}
	//	printf("dfaAfterRightTrimBeforeMinimize\n");
	//	dfaPrintGraphviz(result, len, indices);
	free(exeps);
	//printf("FREE ToState\n");
	free(to_states);
	//printf("FREE STATUCES\n");
	free(statuces);
	free(indices);

	return result;

}

int main(int argc, const char *argv[]) {

	//Output verification result
	FILE *fopen();
	out = stdout;

	//up to three DFAs as input
	DFA *resultDFA = NULL;
	DFA* M[3]; //up to three dfa used
	int i, j;
	int resultBool = -1; //unknown
	int *offsets = NULL;
	int* indices_main;
    i = 1;
	if (argv[i][1] == 'b') {
		dfaOption |= MASK_CONSTRUCT;
	} else if (argv[i][1] == 'u') {
		dfaOption |= MASK_UNION;
	} else if (argv[i][1] == 'i') {
		dfaOption |= MASK_INTERSECT;
	} else if (argv[i][1] == 'n') {
		dfaOption |= MASK_NEGATE;
	} else if (argv[i][1] == 'c') {
		dfaOption |= MASK_CONCAT;
	} else if (argv[i][1] == 'r') {
		dfaOption |= MASK_REPLACE;
	} else if (argv[i][1] == 't') {
		dfaOption |= MASK_TEST;
	} else if (argv[i][1] == 'v') {
		offsets = (int *) malloc(sizeof(int) * NUMBEROFVARIABLES);
		for (j = 0; j < NUMBEROFVARIABLES; j++)
			offsets[j] = 0;
		if (argv[i][2] == '1')
			dfaOption |= MASK_EMPTYCHECK;
		else if (argv[i][2] == '2')
			dfaOption |= MASK_INTERCHECK;
		else if (argv[i][2] == '3')
			dfaOption |= MASK_EQUALCHECK;
		else if (argv[i][2] == '4')
			dfaOption |= MASK_INCLUDECHECK;
	} else {
		printf(" We intend to support the following DFA operations:");
		printf(
				"\n\t [-b OutputFileName InputFileName1]: output a DFA to OutputFileName from InputFileName1");
		printf("\n\t [-t]: test");
		printf(
				"\n\t [-u OutputFileName InputFileName1 InputFileName2]: output UNION(InputFileName1, InputFileName2) to OutputFileName");
		printf(
				"\n\t [-i OutputFileName InputFileName1 InputFileName2]: output INTERSECT(InputFileName1, InputFileName2) to OutputFileName");
		printf(
				"\n\t [-n OutputFileName InputFileName1]: output NEGATE(InputFileName1) to OutputFileName");
		printf(
				"\n\t [-c OutputFileName InputFileName1 InputFileName2]: output CONCATENATE(InputFileName1, InputFileName2) to OutputFileName");
		printf(
				"\n\t [-r OutputFileName InputFileName1 InputFileName2 InputFileName3]: output REPLACE(InputFileName1, InputFileName2, InputFileName3) to OutputFileName");
		printf(
				"\n\n We also intend to support the following verification options:");
		printf(
				"\n\t [-v1 OutputFileName InputFileName1]: Check whether InputFileName1 is empty.");
		printf(
				"\n\t [-v2 OutputFileName InputFileName1 InputFileName2]: Check whether InputFileName1 and InputFileName2 are intersected.");
		printf(
				"\n\t [-v3 OutputFileName InputFileName1 InputFileName2]: Check whether InputFileName1 and InputFileName2 are equal.");
		printf(
				"\n\t [-v4 OutputFileName InputFileName1 InputFileName2]: Check whether InputFileName1 is included in InputFileName2.\n\n");
		exit(1);
	}

	indices_main = allocateAscIIIndexWithExtraBit(NUM_ASCII_TRACKS);
	switch (dfaOption) {
	case MASK_CONSTRUCT:
		//need to be implemented: reading a string from a file
		resultDFA = dfa_construct_char('a', NUM_ASCII_TRACKS, indices_main);
		break;
	case MASK_TEST:
		//dfa_test_pre_image(NUM_ASCII_TRACKS, indices_main);
		dfa_test_strrchr(5); // WORKING :) - Reaching a fixed point! Assertion Proven!
		dfa_test_gxine_ok(); // ERROR IN MONA - makebasic.c:41: failed invariant - please inform mona@brics.dk

		dfa_test_gxine(); // ERROR IN MONA - makebasic.c:41: failed invariant - please inform mona@brics.dk

		dfa_test_myez(); // ERROR IN MONA - makebasic.c:41: failed invariant - please inform mona@brics.dk

		dfa_test_samba(); // ERROR IN MONA - makebasic.c:41: failed invariant - please inform mona@brics.dk

		dfa_test_strlen(); // WORKING :) - Assertion Proven!

		dfa_test_length(8, indices_main); // NOW ==> WORKING :) - Previously ==> ERROR : strange: ../stranger_lib.c:3035: getSemilinerSetCoefficients: Assertion `sink > -1' failed.

		dfa_test_arith(2); // WORKING :)

		dfa_test_basic(NUM_ASCII_TRACKS, indices_main); // WORKING :)
		dfa_test_vul1(NUM_ASCII_TRACKS, indices_main); // ERROR IN MONA - makebasic.c:41: failed invariant - please inform mona@brics.dk
		dfa_test_vul1_saint(NUM_ASCII_TRACKS, indices_main); // ERROR IN MONA - makebasic.c:41: failed invariant - please inform mona@brics.dk
		dfa_test_vul2(NUM_ASCII_TRACKS, indices_main); // WORKING :)  (Vulnerable)
		dfa_test_vul2_saint(NUM_ASCII_TRACKS, indices_main); // WORKING :)  (Secure)
		dfa_test_vul3(NUM_ASCII_TRACKS, indices_main); // WORKING :)  (Vulnerable)
		dfa_test_vul3_saint_fail(NUM_ASCII_TRACKS, indices_main); // WORKING :)  (Vulnerable)
		dfa_test_vul3_saint(NUM_ASCII_TRACKS, indices_main); // WORKING :)  (Secure)
		dfa_test_vul4(NUM_ASCII_TRACKS, indices_main); // WORKING :)  (Vulnerable)
		dfa_test_vul4_saint(NUM_ASCII_TRACKS, indices_main); // ERROR IN MONA - makebasic.c:201: failed invariant - please inform mona@brics.dk
		dfa_test_vul5(NUM_ASCII_TRACKS, indices_main); // WORKING :) Result1: Vulnerable! - Result2: Vulnerable! - Result3: Vulnerable!
		dfa_test_vul5_saint(NUM_ASCII_TRACKS, indices_main); // ERROR IN MONA - makebasic.c:201: failed invariant - please inform mona@brics.dk
		dfa_test_vul6(NUM_ASCII_TRACKS, indices_main); // ERROR IN MONA - makebasic.c:201: failed invariant - please inform mona@brics.dk
		dfa_test_vul6_saint(NUM_ASCII_TRACKS, indices_main); // ERROR IN MONA - makebasic.c:201: failed invariant - please inform mona@brics.dk
		dfa_test_multi_signature(NUM_ASCII_TRACKS, indices_main); // WORKING :)
		dfa_test_multi_signature_vul03(NUM_ASCII_TRACKS, indices_main); // WORKING :)
		dfa_test_multi_signature_vul05(NUM_ASCII_TRACKS, indices_main); // WORKING :)
//		 	dfa_test_three_inputs_signature(NUM_ASCII_TRACKS, indices_main);

		test_dfa_construct_from_automaton(NUM_ASCII_TRACKS, indices_main);

		break;
	case MASK_UNION:
		M[0] = dfa_construct_string("foo", NUM_ASCII_TRACKS, indices_main);
		M[1] = dfa_construct_string("bar", NUM_ASCII_TRACKS, indices_main);
		resultDFA = dfa_union(M[0], M[1]);
		break;
	case MASK_INTERSECT:
		M[0] = dfa_construct_string("foo", NUM_ASCII_TRACKS, indices_main);
		M[1] = dfa_construct_string("bar", NUM_ASCII_TRACKS, indices_main);
		resultDFA = dfa_intersect(M[0], M[1]);
		break;
	case MASK_NEGATE:
		M[0] = dfa_construct_string("foo", NUM_ASCII_TRACKS, indices_main);
		resultDFA = dfa_negate(M[0], NUM_ASCII_TRACKS, indices_main);
		break;
	case MASK_CONCAT:
		M[0] = dfa_construct_string("foo", NUM_ASCII_TRACKS, indices_main);
		M[1] = dfa_construct_string("bar", NUM_ASCII_TRACKS, indices_main);
		resultDFA = dfa_concat(M[0], M[1], NUM_ASCII_TRACKS, indices_main);
		break;
	case MASK_REPLACE:
		M[0] = dfa_construct_string("foo", NUM_ASCII_TRACKS, indices_main);
		M[1] = dfa_construct_string("bar", NUM_ASCII_TRACKS, indices_main);
		M[2] = dfa_construct_string("foobar", NUM_ASCII_TRACKS, indices_main);
		resultDFA = dfa_replace(M[0], M[1], M[2],
		NUM_ASCII_TRACKS, indices_main);
		break;
	case MASK_EMPTYCHECK:
		M[0] = dfaASCIINonString(NUM_ASCII_TRACKS, indices_main);
		resultBool = check_emptiness(M[0], NUM_ASCII_TRACKS, indices_main);
		break;
	case MASK_INTERCHECK:
		M[0] = dfa_construct_string("foo", NUM_ASCII_TRACKS, indices_main);
		char *foobar[2];
		foobar[0]= "foo";
		foobar[1]= "bar";
		M[1] = dfa_construct_set_of_strings(foobar,2, NUM_ASCII_TRACKS, indices_main);
		resultBool = check_intersection(M[0], M[1],
				NUM_ASCII_TRACKS, indices_main);
		break;
	case MASK_EQUALCHECK:
		M[0] = dfa_construct_string("foo", NUM_ASCII_TRACKS, indices_main);
		M[1] = dfa_construct_string("foo", NUM_ASCII_TRACKS, indices_main);
		resultBool = check_equivalence(M[0], M[1], NUM_ASCII_TRACKS,
				indices_main);
		break;
	case MASK_INCLUDECHECK:

		M[0] = dfa_construct_string("foo", NUM_ASCII_TRACKS, indices_main);
		char *foobar2[2];
		foobar2[0]= "foo";
		foobar2[1]= "bar";
		M[1] = dfa_construct_set_of_strings(foobar2,2, NUM_ASCII_TRACKS, indices_main);
		resultBool = check_inclusion(M[0], M[1], NUM_ASCII_TRACKS, indices_main);
		break;
	}

	if (dfaOption
			& (MASK_CONSTRUCT | MASK_UNION | MASK_INTERSECT | MASK_NEGATE
					| MASK_CONCAT | MASK_REPLACE)) {
		dfaPrintVerbose(resultDFA);
		dfaFree(resultDFA);
	} else if (dfaOption
			& (MASK_EMPTYCHECK | MASK_INTERCHECK | MASK_EQUALCHECK
					| MASK_INCLUDECHECK)) {
		if (resultBool > 0)
			printf("\n Verification Result: True\n");
		else if (resultBool == 0)
			printf("\n Verification Result: False\n");
		else
			printf("\n Verification Result: Unknown\n");
	}
	//if(resultDFA) dfaFree(resultDFA);
	free(indices_main);
	printf(
			"\n\n\n==================================================================\n");
	printf("Test passed :)\n");
	printf(
			"==================================================================\n");
	return resultBool;
}

