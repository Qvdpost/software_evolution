module metrics::lines_of_code

import IO;
import Set;
import List;
import Map;
import String;
import Exception;
import Location;
import lang::java::m3::Core;
import lang::java::m3::AST;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;

// Counts lines of comments preceding ast nodes.
tuple[int, int] countComments(loc src) {
	list[str] lines = readFileLines(src);
	int line_count = 0;
	int char_count = 0;
	
	int newline = 1;
	
	bool open_comment = false;
	for (line <- lines) {
		if (/^\s*\/\// := line) {
			line_count += 1;
			char_count += size(line) + 2;
		} else if (/^\s*\/\*/ := line) {
			line_count += 1;
			char_count += size(line) + 2;	
			open_comment = true;
		} else if (/^\s*\*\// := line) {
			line_count += 1;
			char_count += size(line) + 2;	
			open_comment = false;
		} else if (open_comment) {
			line_count += 1;
			char_count += size(line) + 2;
		} else 
			return <line_count, char_count>;
	}
	return <line_count, char_count>;
}

str getTrailingText(loc src) {
	str line = "";
	src.length = 2;
	str char = getContent(src);
	while (char != "", !/\n/ := char) {
		line += char;
		src.offset += 2;
		char = getContent(src);
	}

	return line;
}

str getPrecedingText(loc src) {
	str line = "";
	src.length = 1;
	str char = getContent(src);	
	while (char != "\n") {
		line += char;
		src.offset -= 1;
		char = getContent(src);
	}

	return reverse(line);
}

private str consumeLine(loc src) {
	list[str] lines = readFileLines(src);
		
	if (lines == [])
		return "";
	
	if (lines[0] == "")
		return "";
		
	if (size(lines) < 2) {
		if (size(lines[0]) < src.length)
			return lines[0];
		src.length += 12;
		return consumeLine(src);
	}
	

	return lines[0];
}

private map[tuple[int, str], loc] addBeginLine(map[tuple[int, str], loc] lines, loc src) {

	src.offset -= src.begin.column;
	src.length = 1;
	src.begin.column = 0;
	src.end.line = src.begin.line;
	src.end.column = 1;
	
	str line = consumeLine(src);
	
		
	
	src.end.column = size(line);
	src.length = size(line);
	
	//println("<line> at <src>");
	
	lines[<src.begin.line, src.path>] = src;
	
	return lines;
}

private map[tuple[int, str], loc] addEndLine(map[tuple[int, str], loc] lines, loc src) {
	// Throw away any preceding lines of a node and start at the last character.
	src.begin.column = src.end.column - 1;
	src.begin.line = src.end.line;
	src.offset += src.length - 1;
	src.length = 1;
	
	str line = consumeLine(src);

	int preceding_length = size(getPrecedingText(src));
	
	// Consume any preceding code on the line.
	src.begin.column = 1;
	src.offset -= preceding_length - 1;
	src.length = preceding_length;

	// Consume the full line in case there was trailing text.
	if (line != "") {
		src.end.column += size(line);
		src.length += size(line) - 1;
	}
	
	//println("<getContent(src)> at <src>");
		
	lines[<src.end.line, src.path>] = src;
	
	return lines;
}


private map[tuple[int, str], loc] updateLOCLines(map[tuple[int, str], loc] lines, node ast_node) {
	loc src = |unknown:///|;
	try
		if (loc node_src := ast_node.src) src = node_src;
	catch NoSuchField("src"): src = |unknown:///|;
	
	
	// This happens for package imports.
	if (src == |unknown:///|)
	{
		return lines;
	}
	
	// If a node has already been added to the LOC (its end line should be present.
	if (<src.end.line, src.path> in lines) {
		return lines;
	}
	
	// The Rascal AST counts preceding lines of comments in the node begin.line value.
	if (src.end.line != src.begin.line) {
		src.offset -= src.begin.column;
		src.length += src.begin.column;
		src.begin.column = 0;
		tuple[int line_count, int char_count] comment = countComments(src);

		if (comment[0] > 0) {
			src.begin.line += comment.line_count;
			src.offset += comment.char_count;
			src.length -= comment.char_count;
			src.begin.column = 0;
		}
	}
		
	lines = addBeginLine(lines, src);
	
	if (src.end.line - src.begin.line != 0) {
		
		lines = addEndLine(lines, src);
	}
	
	
	return lines;
}

map[tuple[int, str], loc] getLOC(list[Declaration] asts) {
	map[tuple[int, str], loc] LOCLines = ();
	visit(asts){
		case \Statement ast_node: LOCLines = updateLOCLines(LOCLines, ast_node);
		case \Declaration ast_node: LOCLines =  updateLOCLines(LOCLines, ast_node);
		case \Expression ast_node: LOCLines = updateLOCLines(LOCLines, ast_node);
	}
	
	return LOCLines;
}

tuple[str, bool] getCode(str line, bool openComment) {
	line = trim(line);
//	if (!openComment, /^\/\// := line)
//		return <"", openComment>;
//	
//	str multiStart = "";
//	str multiEnd = "";
//	if ( !openComment, /<begin:.*>\/\*<rest:.*>/ := line) {
//		multiStart = trim(begin);
//		line = rest;
//		openComment = true;
//	}
//
//	if (!openComment, multiStart == "") {
//		return <line, openComment>;
//	}
//	
//	if (/\*\/<end:.*>/ := line) {
//		multiEnd = trim(end);
//		openComment = false;
//	}

	cleanCode = visit(line) {
		case /^".*"/ => ""
	}

	str code = ""; 
	if (openComment, /\*\/<rest:.*>/ := line) {
		line = rest;
	}
	// Check if a open multiline comment is closed
	openComment = openComment && !/[^\/\*]{0,1}\*\// := cleanCode;
	

	if (!openComment)
		code = visit(line){
			case /^<literal:".*">/ => literal
			case /^\/\*.*\*\// => ""
			case /^\/\*.*/ => ""
			case /^\/\*.*[^\*\/]/ => ""
		}
	
	// Check for opening multiline comment
	if (/\/\*<rest:.*>/ := cleanCode, !/\*\// := rest)
		openComment = true;
	
		
	return <code, openComment>;

}

map[str, map[int, map[loc, str]]] getLOCFromFile(loc file) {
	map[str, map[int, map[loc, str]]] locLines = (file.path: ());
	int offset = 0;
	int line_number = 1;
	bool openComment = false;
	
	for (line <- readFileLines(file)) {
		int line_len = size(line);
		
		tuple[str code, bool comment] codeLine = getCode(line, openComment);
		openComment = codeLine.comment;
		
		
		if (codeLine.code != "")
			locLines[file.path][line_number] = (file(offset, line_len,<line_number,0>,<line_number, line_len>): codeLine.code);
			
		offset += line_len + 2;
		line_number += 1;
	}
	
	return locLines;
}

map[str, map[int, map[loc, str]]] getRegexLOC(loc projectLocation) {
	M3 model = createM3FromEclipseProject(projectLocation);
	// map[file_path, map[line_number, map[loc, code]]]
	map[str, map[int, map[loc, str]]] LOCLines = ();
	
	for (m <- model.containment, m[0].scheme == "java+compilationUnit"){
		LOCLines += getLOCFromFile(m[0]);
	}
	
	return LOCLines;
}

int getLOCCount(list[Declaration] asts){
	return size(getLOC(asts));
}

map[Declaration, int] getUnitSize(list[Declaration] subtrees) {
	map[Declaration, int] result = ();
	for (subtree <- subtrees) {
		result[subtree] = getLOCCount([subtree]);
	}
	return result;
}

