module metrics::clones

import IO;
import Set;
import List;
import Map;
import String;
import Location;
import Node;
import lang::java::m3::Core;
import lang::java::m3::AST;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;
import metrics::ast_reader;
import metrics::lines_of_code;
import metrics::duplicates;
import metrics::complexity;

bool isVarType(Expression expr) {
	if (expr.decl.scheme == "java+variable")
		return true;
		
	if (expr.decl.scheme == "java+field")
		return true;
		
	if (\variable(_, _) := expr)
		return true;
		
	return false;
}

str typToString(TypeSymbol typ) {
	switch (typ) {
		case \class(_, _): return "class";
  		case \interface(_, _): return "interface";
  		case \enum(_): return "enum";
  		case \method(_, _, _, _): return "method";
  		case \constructor(_, _): return "cons";
  		case \typeParameter(_, _): "typeParam"; 
  		case \typeArgument(_): return "typeArg";
  		case \wildcard(_): return "wildcard";
  		case \capture(_, _): return "capture";
  		case \intersection(_): return "intersection";
  		case \union(_): return "union";
  		case \object(): return "object";
  		case \int(): return "int";
  		case \float(): return "float";
  		case \double(): return "double";
  		case \short(): return "short";
  		case \boolean(): return "bool";
  		case \char(): return "char";
  		case \byte(): return "byte";
  		case \long(): return "long";
  		case \void(): return "void";
  		case \null(): return "null";
  		case \array(_, _): return "array";
  		case \typeVariable(_): return "typeVar";
  		case \unresolved(): return "unresolved";
		default: return "unknown";
	}
	return "";
}

str replaceVarName(str word, Expression expr) {
	if (\qualifiedName(_, _) := expr)
		return "__qualifiedName__";
	if (word == expr.name) 
		return "__" + typToString(expr.typ) + "__";
	
	return word;
}

bool isSubsumed(set[loc] a, set[loc] b) {
	for (src <- a) {
		bool subsumed = false;
		for (other <- b) {
			if (isStrictlyContainedIn(src, other)) {
				subsumed = true;
				break;
			}
		}
		if (!subsumed)
			return false;
	}
	return true;
}

bool checkSubsumption(tuple[node tree, set[loc] locs] a, set[set[loc]] targets) {
	for (target <- targets) {
		if (isSubsumed(a.locs, target)) {
			return true;
		}
	}
	return false;
}

map[node, set[loc]] filterTreeSubsumption(list[tuple[node tree, set[loc] locs]] pairs, set[set[loc]] targets) {
	if (isEmpty(pairs))
		return ();
		
	tuple[node tree, set[loc] locs] pair = head(pairs);
	if (!checkSubsumption(pair, targets))
		return (pair.tree: pair.locs) + filterTreeSubsumption(tail(pairs), targets);
	else
		return filterTreeSubsumption(tail(pairs), targets - {pair.locs});
}

Expression anonymizeVar(Expression expr) {
	if (expr@name ?)
		expr.name = replaceVarName(expr.name, expr);
		
	return expr;
}

int mass(node tree) {
	int treeMass = 0;
	
	visit(tree) {
		case node child: {
			treeMass += 1;	
		}
	}
	
	return treeMass;

}

list[Statement] flattenBlock(list[Statement] unitBlock) {
	list[Statement] unit_body = [];
	
	for (statement <- unitBlock) {
		switch (statement) {
			case state:\block(list[Statement] statements): unit_body += flattenBlock(statements);
			case state:\foreach(Declaration parameter, Expression collection, \block(body)): {
				foreach_node = state;
				foreach_node[2] = \empty();
				unit_body += foreach_node + flattenBlock(body);
			}
			case state:\for(list[Expression] initializers, Expression condition, list[Expression] updaters, \block(body)): {
				for_node = state;
				for_node[3] = \empty();
				unit_body += for_node + flattenBlock(body);
			}
			case state:\for(list[Expression] initializers, list[Expression] updaters, \block(body)): {
				for_node = state;
				for_node[2] = \empty();
				unit_body += for_node +  flattenBlock(body);
			}
			case state:\if(Expression condition, \block(thenBranch)): {
				if_node = state;
				if_node[1] = \empty();
				unit_body += if_node +  flattenBlock(thenBranch);
			}
			case state:\if(Expression condition, \block(thenBranch), \block(elseBranch)): {
				if_node = state;
				if_node[1] = \empty();
				if_node[2] = \empty();
				else_node = setKeywordParameters(\expressionStatement(\simpleName("__elseBranch__")), ("src": state.src));
				unit_body += if_node +  flattenBlock(thenBranch) + else_node + flattenBlock(elseBranch);
			}
			case state:\if(Expression condition, \block(thenBranch), elseBranch): {
				if_node = state;
				if_node[1] = \empty();
				if_node[2] = \empty();
				else_node = setKeywordParameters(\expressionStatement(\simpleName("__elseBranch__")), ("src": state.src));
				unit_body += if_node +  flattenBlock(thenBranch) + else_node + flattenBlock([elseBranch]);
			}
			case state:\switch(Expression expression, list[Statement] statements): {
				switch_node = state;
				switch_node[1] = [];
				unit_body += switch_node+  flattenBlock(statements);
			}
			case state:\synchronizedStatement(Expression lock, \block(body)): {
				sync_node = state;
				sync_node[1] = \empty();
				unit_body += sync_node +  flattenBlock(body);
			}
			case state:\try(\block(body), list[Statement] catchClauses): {
				try_node = state;
				try_node[1] = [];
				unit_body += try_node + flattenBlock(body) +  flattenBlock(catchClauses);
			}
			case state:\try(\block(body), list[Statement] catchClauses, \block(\finally)): {
				try_node = state;
				try_node[0] = \empty();
				try_node[1] = [];
				try_node[2] = \empty();
				unit_body += try_node +  flattenBlock(body) + flattenBlock(catchClauses) + flattenBlock(\finally);
			}
			case state:\catch(Declaration exception, \block(body)): {
				catch_node = state;
				catch_node[1] = \empty();
				unit_body += catch_node +  flattenBlock(body);
			}
			case state:\while(Expression condition, \block(body)): {
				while_node = state;
				while_node[1] = \empty();
				unit_body += while_node + flattenBlock(body);
			}
			case state:\Statement statement: {
				unit_body += statement;
			}
		}
	}
	
	//visit (block){
	//	case \block(list[Statement] statements): unit_body += flattenBlock(statements);
	//	case \foreach(Declaration parameter, Expression collection, \block(body)): unit_body += [\foreach(parameter, collection, \empty())] + flattenBlock(body);
	//	case \for(list[Expression] initializers, Expression condition, list[Expression] updaters, \block(body)): unit_body += [\for(initializers, condition, updaters, \empty())] + flattenBlock(body);
	//	case \for(list[Expression] initializers, list[Expression] updaters, \block(body)): unit_body += [\for(initializers, updaters, \empty())] +  flattenBlock(body);
	//	case \if(Expression condition, \block(thenBranch)): unit_body += [\if(condition, \empty())] +  flattenBlock(thenBranch);
	//	case \if(Expression condition, \block(thenBranch), \block(elseBranch)): unit_body += [\if(condition, \empty(), \empty())] +  flattenBlock(thenBranch) + flattenBlock(elseBranch);
	//	case \switch(Expression expression, list[Statement] statements): unit_body += [\switch(expression, [])] +  flattenBlock(statements);
	//	case \synchronizedStatement(Expression lock, \block(body)): unit_body += [\synchronizedStatement(lock, \empty())] +  flattenBlock(body);
	//	case \try(\block(body), list[Statement] catchClauses): unit_body += [\try(\empty(), []), flattenBlock(body)] +  flattenBlock(catchClauses);
	//	case \try(\block(body), list[Statement] catchClauses, \block(\finally)): unit_body += [\try(\empty(), [], \empty())] +  flattenBlock(body) + flattenBlock(catchClauses) + flattenBlock(\finally);
	//	case \catch(Declaration exception, \block(body)): unit_body += [\catch(exception, \empty())] +  flattenBlock(body);
	//	case \while(Expression condition, \block(body)): unit_body += [\while(condition, \empty())] + flattenBlock(body);
	//	case \Statement statement: unit_body += statement;
	//}
	
	return unit_body;
}

void getClonesType2(loc projectLocation) {
	
	list[Declaration] asts = getASTs(projectLocation);
	
	list[Declaration] units = getMethods(asts);
	
	// Modify ast for clone detection.
	//units = visit(units){
	//	case \Expression expr => anonymizeVar(expr)
	//}
	
	// Flatten units
	units = top-down visit(units){
		case mthd:\method(_, _, _, _, \block(statements)): {
			mthd[4] = \block(flattenBlock(statements));
			insert mthd;
		}
	}
	
	map[node, set[loc]] subTrees = ();
	
	// Add subtrees to map.
	println("Finding duplicate subtrees");
	for (unit <- units) {
		if (Statement body := unit[4])
			if (list[Statement] statements := body[0])
				for (treeEnd <- [6..size(statements)]) {
					for (treeStart <- [0..treeEnd+1]) {
						src = cover([statements[treeStart].src, statements[treeEnd].src]);
							
						node subTree = makeNode("subTree", \block(statements[treeStart..treeEnd+1]));
						subTree = unsetRec(subTree, {"src", "decl"});
						
						if (subTree in subTrees)
							subTrees[subTree] += src;
						else
							subTrees[subTree] = {src};
							
						//println(subTree);
						//println(src);
						//println("=============");
					}
				}
		//for {start <- [0..range(unit[4]
		//if (mass(subTree) >= 12) {
		//	loc src = |unknown:///|;
		//	if (subTree@src ?, loc node_src := subTree.src)
		//		src = node_src;
		//		
		//	subTree = unsetRec(subTree, {"src", "decl"});
		//					
		//	if (subTree in subTrees)
		//		subTrees[subTree] += src;
		//	else
		//		subTrees[subTree] = {src};
		//		
		//	println(subTree);
		//	println(src);
		//}
	}
	//visit(units) {
	//	case node subTree: {	
	//		
	//		if (mass(subTree) >= 12) {
	//		
	//			loc src = |unknown:///|;
	//			if (subTree@src ?, loc node_src := subTree.src)
	//				src = node_src;
	//				
	//			subTree = unsetRec(subTree, {"src", "decl"});
	//							
	//			if (subTree in subTrees)
	//				subTrees[subTree] += src;
	//			else
	//				subTrees[subTree] = {src};
	//				
	//			println(subTree);
	//			println(src);
	//				
	//			//if (getName(subTree) == "block") {
	//			//	if (list[node] statements := subTree[0]){
	//			//		for (index <- [1..size(statements) + 1]) {
	//			//			Statement blockTree = \block(statements[index..]);	
	//			//			if (blockTree in subTrees)
	//			//				subTrees[blockTree] += src;
	//			//			else
	//			//				subTrees[blockTree] = {src};				
	//			//		}
	//			//	}
	//			//}
	//		}
	//	}
	//}
	
	//println(subTrees);
	
	subTrees = (key: subTrees[key] | key <- subTrees, size(subTrees[key]) > 1);
	
	subTrees = filterTreeSubsumption(toList(subTrees), range(subTrees));
	
	for (subTree <- subTrees) {
		if (|unknown:///| notin subTrees[subTree], subTrees[subTree] != {})
			println("<subTree> @ <subTrees[subTree]>");
			println("---");
	}
	
}

map[list[str], set[loc]] getClonesType1(map[str, map[int, map[loc, str]]] locLines) {
		
	for (file <- locLines, fileLOC := locLines[file]) {
		for  (line_number <- fileLOC, lineLOC := fileLOC[line_number]) {
			for (src <- lineLOC, code := lineLOC[src]) {
				locLines[file][line_number][src] = replaceAll(code, " ", "");
			}
		}	
	}
	
	// Map all lines and occurrences
	map[list[str], set[list[loc]]] duplicates = ();
		
	println("Setting up code lines and metadata");
	for (file <- locLines, fileLOC := locLines[file]) {
		for  (line_number <- locLines[file], lineLOC := fileLOC[line_number]) {
			for (src <- lineLOC, code := lineLOC[src]) {
				if ([code] in duplicates)
					duplicates[[code]] += {[src]};
				else
					duplicates[[code]] = {[src]};
			}
		}	
	}
	
	// Discard all unique lines.
	duplicates = (key: duplicates[key] | key <- duplicates, size(duplicates[key]) > 1);
	
	// Add all largest consecutive lines of code that form a duplicate with another set of lines.
	println("Getting duplicate blocks.");
	duplicates = getDuplicateBlocks(duplicates, locLines);
		
	// Discard all original single lines of duplicate code.
	println("Filtering duplicate blocks");
	map[list[str], set[loc]] duplicate_blocks = ();
	for (codeLine <- duplicates, size(duplicates[codeLine]) > 1, size(codeLine) > 1) {
		duplicate_blocks[codeLine] = {cover([head(locs), last(locs)]) | locs <- (duplicates[codeLine])};
	}
	
	// Discard all blocks contained in other blocks
	duplicate_blocks = filterSubsumption(duplicate_blocks);
	
	num code_count = sum([size(domain(locLines[file])) | file <- locLines]);
	showDuplicateStats(duplicate_blocks, code_count);
	
	return duplicate_blocks;
}