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
		result += line + "\n";
	}
	
	return result;
}

tuple[list[str], list[loc]] getBlock(loc src, map[str, set[loc]] duplicates, map[tuple[int, str], tuple[str, loc]] sourceCode, map[str, int] fileLOC) {
	list[str] block = [sourceCode[<src.begin.line, src.path>][0]];
	list[loc] sources = [src];
	
	int line_number = src.begin.line;
	while (line_number < fileLOC[src.path]) {
		line_number += 1;
		tuple[int, str] next = <line_number, src.path>;
		if (next in sourceCode) {
			// Immediately terminate if the next LOC is not a duplicate.
			if (sourceCode[next][0] notin duplicates) {
				return <block, sources>;
			}
			
			block += sourceCode[next][0];
			sources += sourceCode[next][1];
		} 

	}
		
	return <block, sources>;
}

tuple[list[str], list[loc]] getDuplicateBlock(loc src_block, list[loc] other_blocks) {

	map[str, set[loc]] block_dups = ();
	for (block_size <- [6..size(src_block)]) {

		str block = blockToString(src_block[0..block_size]);
		
		//println("Block: <block> @ <cover(result.src[0..block_size])>");
		for (other_block <- [blockToString(other[0..block_size]) | other <- other_blocks]) {
			;
		}
		if (block notin duplicates)
			duplicates[block] = {cover(result.src[0..block_size])};
		else
			duplicates[block] += {cover(result.src[0..block_size])};	

	}
	
	return <duplicates, true>;
}

map[str, set[loc]] getDuplicateBlocks(list[loc] sources, map[str, set[loc]] duplicates, map[tuple[int, str], tuple[str, loc]] sourceCode, map[str, int] fileLOC) {
		
	list[tuple[list[str] code, list[loc] locs]] blocks = [block | src <- sources, block := getBlock(src, duplicates, sourceCode, fileLOC), size(block[0]) >= 6];
	
	if (blocks == [])
		return duplicates;
		
	for (block_size <- {size(block) | block <- blocks.code}) {
		for (tuple[list[str] code, list[loc] locs] block <- blocks) {
			str code_block = blockToString(block.code[0..block_size]);
			loc loc_block = cover(block.locs[0..block_size]);
			if (code_block notin duplicates)
				duplicates[blockToString(block.code[0..block_size])] = {loc_block};
			else
				duplicates[blockToString(block.code[0..block_size])] += {loc_block};
		}
	}	
	
	return duplicates;
}

bool isStrictSuperBlock(loc src, list[loc] others) {
	for (other <- others) {
		if (isStrictlyContainedIn(src, other)) {
			return false;
		}
	}
	return true;
}

void getDuplicates(list[Declaration] asts) {
	// Fetch all lines of code and their locations.
	println("Fetching code lines");
	map[tuple[int, str], loc] LOCLines = getCodeLines(asts);
	
	list[tuple[str, loc]] codeLines = [];
	println("Trimming and cleaning up");
	int loclines_count = size(LOCLines);
	for (locline <- LOCLines) {
		if (loclines_count % 1000 == 0)
			println("<loclines_count> lines to go.");
		loclines_count -=1;
		codeLines += <trim(getContent(LOCLines[locline])), LOCLines[locline]>;
		//if (trim(getContent(LOCLines[locline])) == "}")
		//	println("<trim(getContent(LOCLines[locline]))> : <LOCLines[locline]>");
	}
	

	// Map all lines and occurrences
	map[str, set[loc]] duplicates = ();
	
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
		if (line.code notin duplicates)
			duplicates[line.code] = {line.src};
		else
			duplicates[line.code] += line.src;
			
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
	int dup_line_count = size(duplicates);
	for (code <- [dup | dup <- duplicates]) {
		if (dup_line_count % 1000 == 0)
			println("Dups to go: <dup_line_count>");
		dup_line_count -= 1;
		duplicates = getDuplicateBlocks(toList(duplicates[code]), duplicates, sourceCode, fileLOC);

	}
		
	// Discard all original single lines of duplicate code.
	dup_count = 0;
	map[str, set[loc]] duplicate_blocks = ();
	for (codeLine <- duplicates, size(duplicates[codeLine]) > 1, size(split("\n", codeLine)) > 1) {
		//println("Dup: \'<codeLine>\' @ <duplicates[codeLine]>");
		//println("");
		duplicate_blocks[codeLine] = duplicates[codeLine];
		dup_count += size(duplicates[codeLine]);
	}
	
	println("Unique duplicates: <size(duplicate_blocks)>");
	println("Total duplicates: <dup_count>");
	
	map[loc, str] duplicate_locs = ();
	
	for (codeBlock <- duplicate_blocks) {
		for (block_loc <- duplicate_blocks[codeBlock]) {
			duplicate_locs[block_loc] = codeBlock;
		}
	}
	
	println("Checking for strict super blockness");
	int block_check_count = size(duplicate_locs);
	for (block_loc <- duplicate_locs) {
		if (block_check_count % 1000 == 0)
			println("<block_check_count> block checks to go.");
		block_check_count -= 1;
		if (!isStrictSuperBlock(block_loc, [key | key <- duplicate_locs])) {
			duplicate_blocks[duplicate_locs[block_loc]] -= block_loc;
		}
	}
	
	dup_count = 0;
	dup_line_count = 0;
	println("Calculating final duplicate blocks");
	for (codeBlock <- duplicate_blocks) {
		dup_count += size(duplicate_blocks[codeBlock]);
		dup_line_count += size(split("\n", codeBlock)) * size(duplicate_blocks[codeBlock]);
		if (duplicate_blocks[codeBlock] != {}) {
			//println("Dup block: \'<codeBlock>\' @ <duplicate_blocks[codeBlock]>");
			println("Dup blocks @ <duplicate_blocks[codeBlock]>");
			println("");
		}
	}
	
	//duplicate_locs = (block_loc: duplicate_locs[block_loc] | block_loc <- duplicate_locs, isStrictSuperBlock(block_loc, domain(duplicate_locs)));
	
	println("Unique duplicates: <size(duplicate_blocks)>");
	println("Total duplicates: <dup_count>");
	println("Total duplicate lines: <dup_line_count>");

	// Start from each duplicate and continue a block of 6 from other occurrences

}