/*
 * test_stranger.c
 *
 *  Created on: Feb 13, 2014
 *      Author: muath
 */
#include <stranger/stranger.h>
#include <stranger/stranger_lib_internal.h>
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

void reset_coeffs(int* coeffs, int var) {
	int i;
	for (i = 0; i < 2 * var; i++)
		coeffs[i] = 0;
}

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

int main(int argc, char**argv) {
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
	attack = dfa_concat_extrabit(dfaAllStringASCIIExceptReserveWords(svar,
			sindices), dfa_construct_string("<script ", svar, sindices), svar,
			sindices);
	attack = dfa_concat_extrabit(attack, dfaAllStringASCIIExceptReserveWords(
			svar, sindices), svar, sindices);

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
	M[0] = dfa_concat_extrabit(M[0],
			dfa_construct_string(": ", svar, sindices), svar, sindices);
	M[0] = dfa_concat_extrabit(M[0], M[3], svar, sindices);
	M[0] = dfa_concat_extrabit(M[0], dfa_construct_string("</td>", svar,
			sindices), svar, sindices);

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
		printf("Result: error!\n");

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

	return 0;
}

