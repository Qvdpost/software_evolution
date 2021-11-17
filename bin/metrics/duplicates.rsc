module metrics::duplicates

import IO;
import Set;
import List;
import Map;
import String;
import Location;
import lang::java::m3::Core;
import lang::java::m3::AST;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;
import metrics::lines_of_code;


list[str] readSources(list[loc] paths) {
	list[str] lines = [];
	for (path <- paths) {
		lines += readFileLines(path);
	}
	return lines;
}

str blockToString(list[str] block) {
	str result = "";
	
	for (line <- block) {
		result += trim(line) + "\n";
	}
	
	return result;
}

tuple[list[str], list[loc]] getBlock(loc src, map[list[str], set[loc]] duplicates, map[tuple[int, str], tuple[str, loc]] sourceCode, map[str, int] fileLOC) {
	list[str] block = [sourceCode[<src.begin.line, src.path>][0]];
	list[loc] sources = [src];
	
	int line_number = src.begin.line;
	while (line_number < fileLOC[src.path]) {
		line_number += 1;
		tuple[int, str] next = <line_number, src.path>;
		
		if (next in sourceCode) {
			// Immediately terminate if the next LOC is not a duplicate.
			if ([sourceCode[next][0]] notin duplicates) {
				return <block, sources>;
			}
			
			block += sourceCode[next][0];
			sources += sourceCode[next][1];
		} 

	}
		
	return <block, sources>;
}

map[list[str], set[loc]] getDuplicateBlock(tuple[list[str] code, list[loc] srcs] block, map[list[str], set[loc]] duplicates, map[tuple[int, str], tuple[str, loc]] sourceCode, map[str, int] fileLOC) {
	int block_len = size(block.code);
	for (sub_block_size <- [0..block_len - 6 + 1], block_len >= 6) {
		for (block_size <- [6+sub_block_size..block_len+1]) {
			list[str] code_block = block.code[sub_block_size..block_size];
			loc loc_block = cover(block.srcs[sub_block_size..block_size]);
			
			if (code_block notin duplicates)
				duplicates[code_block] = {loc_block};
			else
				duplicates[code_block] += {loc_block};

		}
	}
	
	return duplicates;
}

map[list[str], set[loc]] getDuplicateBlocks(map[list[str], set[loc]] duplicates, map[tuple[int, str], tuple[str, loc]] sourceCode, map[str, int] fileLOC) {
	int file_count = size(fileLOC);
	for (file <- fileLOC) {
		println("Blocking <file> (<file_count> to go)");
		file_count -= 1;
		int offset = 0;
		
		for (line <- [0..fileLOC[file]+1], line + offset < fileLOC[file]) {
			if (<line + offset, file> in sourceCode, tuple[str content, loc src] code := sourceCode[<line + offset, file>], code.content != "}", [code.content] in duplicates) {
				tuple[list[str] code, list[loc] srcs] block = getBlock(code.src, duplicates, sourceCode, fileLOC);
				int block_len = size(block.code);
					
				duplicates = getDuplicateBlock(block, duplicates, sourceCode, fileLOC);
				
				offset += block_len;
			}
		}
	}
	
	return duplicates;
}

bool isStrictSuperBlock(loc src, set[loc] others) {
	for (other <- others) {
		if (isStrictlyContainedIn(src, other)) {
			return false;
		}
	}
	return true;
}

list[tuple[str, loc]] getCodeLines(map[str, map[int, map[loc, str]]] lines) {
	list[tuple[str, loc]] codeLines = [];
	println("Trimming and cleaning up");
	int loclines_count = size(lines);
	for (locline <- lines) {
		if (loclines_count % 1000 == 0)
			println("<loclines_count> lines to go.");
		loclines_count -=1;
		codeLines += <trim(getContent(lines[locline])), lines[locline]>;
	}
	
	return codeLines;
}

void getDuplicates(map[tuple[int, str], loc] LOCLines) {
	
	list[tuple[str, loc]] codeLines = getCodeLines(LOCLines);
	

	// Map all lines and occurrences
	map[list[str], set[loc]] duplicates = ();
	
	// Keep track of line numbers and their filepaths related to their source code and precise location.
	map[tuple[int, str], tuple[str, loc]] sourceCode = ();
	
	// Remember some meta-data about files (number of code lines).
	map[str, int] fileLOC = ();
	
	int lines_count = size(codeLines);
	println("Setting up code lines and metadata");
	for (tuple[str code, loc src] line <- codeLines) {
		if (lines_count % 1000 == 0)
			println("<lines_count> lines to go.");
		//println("<line.code> @ <line.src>");
		lines_count -=1;
		if ([line.code] notin duplicates)
			duplicates[[line.code]] = {line.src};
		else
			duplicates[[line.code]] += line.src;
			
		sourceCode[<line.src.begin.line, line.src.path>] = <line.code, line.src>;
		
		if (line.src.path notin fileLOC) 
			fileLOC[line.src.path] = line.src.begin.line;
		else
			fileLOC[line.src.path] = max([line.src.begin.line, fileLOC[line.src.path]]);
	}
	
	// Discard all unique lines.
	duplicates = (key: duplicates[key] | key <- duplicates, size(duplicates[key]) > 1);
	
	// Add all largest consecutive lines of code that form a duplicate with another set of lines.
	println("Getting duplicate blocks.");
	duplicates = getDuplicateBlocks(duplicates, sourceCode, fileLOC);


		
	// Discard all original single lines of duplicate code.
	map[list[str], set[loc]] duplicate_blocks = ();
	for (codeLine <- duplicates, size(duplicates[codeLine]) > 1, size(codeLine) > 1) {
		duplicate_blocks[codeLine] = duplicates[codeLine];
	}
	
	map[loc, list[str]] duplicate_locs = ();
	map[str, map[loc, list[str]]] file_block_locs = ();
	
	for (codeBlock <- duplicate_blocks) {
		for (block_loc <- duplicate_blocks[codeBlock]) {
			if (block_loc.path notin file_block_locs)
				file_block_locs[block_loc.path] = ();
				
			file_block_locs[block_loc.path][block_loc] = codeBlock;
			duplicate_locs[block_loc] = codeBlock;
		}
	}
	
	println("Checking for strict super blockness");
	int block_check_count = size(duplicate_locs);
	for (block_loc <- duplicate_locs) {
		if (block_check_count % 1000 == 0)
			println("<block_check_count> block checks to go.");
		block_check_count -= 1;
		
		// Check for size of duplicate_blocks[duplicate_locs[block_loc]] to maintain a trace of duplication.
		if (!isStrictSuperBlock(block_loc, domain(file_block_locs[block_loc.path]))) {
			duplicate_blocks[duplicate_locs[block_loc]] -= block_loc;
		}
	}
	
	num dup_count = 0;
	num dup_line_count = 0;
	println("Calculating final duplicate blocks");
	for (codeBlock <- duplicate_blocks) {
		dup_count += size(duplicate_blocks[codeBlock]);
		dup_line_count += size(codeBlock) * size(duplicate_blocks[codeBlock]);
		if (duplicate_blocks[codeBlock] != {}) {
			println("Dup blocks @ <duplicate_blocks[codeBlock]>");
			println("");
		}
	}
	
	println("Total duplicates: <dup_count>");
	println("Total duplicate lines: <dup_line_count>");
	println("Duplicate percentage: <dup_line_count / size(LOCLines) * 100>%");

	// Start from each duplicate and continue a block of 6 from other occurrences

}