module main

import IO;
import Set;
import List;
import Map;
import lang::java::m3::Core;
import lang::java::m3::AST;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;
import util::Benchmark;

import metrics::ast_reader;
import metrics::complexity;
import metrics::duplicates;
import metrics::lines_of_code;

void main(){
	//loc test_file = |project://series_1/test_data/test.java|;
	//
	//Declaration test_ast = createAstFromFile(test_file, true);
	//
	
	//list[Declaration] test_asts = getASTs(|project://smallsql0.21_src|);
	//list[Declaration] test_asts = getASTs(|project://hsqldb-2.3.1|);
	//list[Declaration] test_asts = getASTs(|project://test_project|);
	
	// Fetch all lines of code and their locations.
	println("Fetching code lines");
	map[str, map[int, map[loc, str]]] LOCLines = getRegexLOC(|project://smallsql0.21_src|);;
	
	//println("Total LOC: <getLOC(test_asts)>");	
	
	//list[Declaration] units = getMethods(test_asts);
	
	//map[Declaration, int] unit_sizes = getUnitSize(units);
	
	//for (statement <- unit_sizes) {
	//	println("Unit LOC: <statement.src> : <unit_sizes[statement]>");
	//}
	
	//map[Declaration, int] unit_complexities = unitComplexity(units);
	
	//for (statement <- unit_complexities) {
	//	println("Unit Complexity: <statement.src> : <unit_complexities[statement]>");
	//}
	
	//println("Complexity rank of project: <complexityRank(test_asts)>");
	int before = userTime();
	getDuplicates(LOCLines);
	println((userTime() - before)/1000000000);
	
	
	return;
}













