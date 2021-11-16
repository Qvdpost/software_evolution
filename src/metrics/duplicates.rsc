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

map[loc, str] mergeBlocks(loc src, map[loc, str] blocks) {
	
	map[loc, str] other_blocks = delete(blocks, src);
	if (isEmpty(other_blocks))
		return blocks;
		
	tuple[loc src, set[loc] blocks] other = takeFirstFrom(domain(other_blocks));
	other_blocks = delete(blocks, other.src);
	
	if (isOverlapping(src, other.src)) {
		loc block = cover([src, other.src]);
		other_blocks[block] = blockToString(readFileLines(block));
		return other_blocks + mergeBlocks(block, other_blocks);
	}

	return (other.src: blocks[other.src]) + mergeBlocks(src, other_blocks);
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

//tuple[list[str], list[loc]] getDuplicateBlock(loc src_block, list[loc] other_blocks) {
//
//	map[str, set[loc]] block_dups = ();
//	for (block_size <- [6..size(src_block)]) {
//
//		str block = blockToString(src_block[0..block_size]);
//		
//		//println("Block: <block> @ <cover(result.src[0..block_size])>");
//		for (other_block <- [blockToString(other[0..block_size]) | other <- other_blocks]) {
//			;
//		}
//		if (block notin duplicates)
//			duplicates[block] = {cover(result.src[0..block_size])};
//		else
//			duplicates[block] += {cover(result.src[0..block_size])};	
//
//	}
//	
//	return <duplicates, true>;
//}

map[str, set[loc]] getDuplicateBlocks(list[loc] sources, map[str, set[loc]] duplicates, map[tuple[int, str], tuple[str, loc]] sourceCode, map[str, int] fileLOC) {
		
	list[tuple[list[str] code, list[loc] locs]] blocks = [block | src <- sources, block := getBlock(src, duplicates, sourceCode, fileLOC), size(block[0]) >= 6];
	
	if (blocks == [])
		return duplicates;
		
	//for (block <- blocks) {
	//	tuple[list[str], list[loc]] dup_block = getDuplicateBlock(block, blocks - block);
	//	
	//	
	//
	//}
		
	for (tuple[list[str] code, list[loc] locs] block <- blocks) {
		map[str, map[loc, list[tuple[list[str], list[loc]]]]] temp_dups;
		
		for (block_size <- [6..size(block.code)+1]) {
			str code_block = blockToString(block.code[0..block_size]);
			loc loc_block = cover(block.locs[0..block_size]);
			
			if (code_block notin temp_dups)
				temp_dups[code_block] = ();
			
			if (loc_block notin temp_dups[code_block])
				temp_dups[code_block][loc_block] = [];
				
			temp_dups[code_block][loc_block] += block;
			
		}
		for (temp_dup <- temp_dups) {
			if (code_block notin duplicates)
				duplicates[blockToString(block.code[0..block_size])] = {loc_block};
			else
				duplicates[blockToString(block.code[0..block_size])] += {loc_block};
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

list[tuple[str, loc]] getCodeLines(map[tuple[int, str], loc] lines) {
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
//	int dup_line_count = size(duplicates);
//	for (code <- [dup | dup <- duplicates]) {
//		if (dup_line_count % 1000 == 0)
//			println("Dups to go: <dup_line_count>");
//		dup_line_count -= 1;
//		duplicates = getDuplicateBlocks(toList(duplicates[code]), duplicates, sourceCode, fileLOC);
//
//	}
	int file_count = size(fileLOC);
	for (file <- fileLOC) {
		println("Blocking <file> (<file_count> to go)");
		file_count -= 1;
		int offset = 0;
		for (line <- [0..fileLOC[file]+1], line + offset < fileLOC[file]) {
			if (<line + offset, file> in sourceCode, tuple[str content, loc src] code := sourceCode[<line + offset, file>], code.content in duplicates) {
				tuple[list[str] code, list[loc] srcs] block = getBlock(code.src, duplicates, sourceCode, fileLOC);
				int block_len = size(block.code);
				int block_size = 6;
				if (block_len >= 6) {
				//for (block_size <- [6..block_len+1], block_len >= 6) {
					str code_block = blockToString(block.code[0..block_size]);
					loc loc_block = cover(block.srcs[0..block_size]);
					
					if (code_block notin duplicates)
						duplicates[code_block] = {loc_block};
					else
						duplicates[code_block] += {loc_block};
				//}
				}
				//offset += block_len;
			}
		}
	}
		
	// Discard all original single lines of duplicate code.
	dup_count = 0;
	map[str, set[loc]] duplicate_blocks = ();
	for (codeLine <- duplicates, size(duplicates[codeLine]) > 1, /\n/ := codeLine) {
		//println("Dup: \'<codeLine>\' @ <duplicates[codeLine]>");
		//println("");
		duplicate_blocks[codeLine] = duplicates[codeLine];
		dup_count += size(duplicates[codeLine]);
	}
	
	println("Unique duplicates: <size(duplicate_blocks)>");
	println("Total duplicates: <dup_count>");
	
	map[loc, str] duplicate_locs = ();
	map[str, map[loc, str]] file_block_locs = ();
	
	for (codeBlock <- duplicate_blocks) {
		for (block_loc <- duplicate_blocks[codeBlock]) {
			if (block_loc.path notin file_block_locs)
				file_block_locs[block_loc.path] = ();
				
			file_block_locs[block_loc.path][block_loc] = codeBlock;
			duplicate_locs[block_loc] = codeBlock;
		}
	}
	
	duplicate_blocks = ();
	println("Merging overlapping blocks");
	for (file <- file_block_locs) {
		int block_count = 0; 
		do {
			block_count = size(file_block_locs[file]);
			for (block_loc <- file_block_locs[file]) {
				file_block_locs[file] = mergeBlocks(block_loc, file_block_locs[file]);
			}
		} while (size(file_block_locs[file]) != block_count);
		
		
		for (block_loc <- file_block_locs[file], code_block := file_block_locs[file][block_loc]) {
			if (code_block notin duplicate_blocks)
				duplicate_blocks[code_block] = {block_loc};
			else
				duplicate_blocks[code_block] += {block_loc};;
		}
	}
	
	//dup_count = 0;
	//dup_line_count = 0;
	//println("Calculating final duplicate blocks");
	//for (file <- file_block_locs) {
	//	for (block_loc <- file_block_locs[file]) {
	//		println("<file_block_locs[file][block_loc]> @ <block_loc>");
	//		println("");
	//		dup_count += size(file_block_locs[file]);
	//		dup_line_count += block_loc.end.line - block_loc.begin.line + 1;
	//	}
	//}
	
	//println("Checking for strict super blockness");
	//int block_check_count = size(duplicate_locs);
	//for (block_loc <- duplicate_locs) {
	//	if (block_check_count % 1000 == 0)
	//		println("<block_check_count> block checks to go.");
	//	block_check_count -= 1;
	//	
	//	if (!isStrictSuperBlock(block_loc, domain(file_block_locs[block_loc.path]))) {
	//		duplicate_blocks[duplicate_locs[block_loc]] -= block_loc;
	//	}
	//}
	//
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
	
	//println("Unique duplicates: <size(duplicate_blocks)>");
	println("Total duplicates: <dup_count>");
	println("Total duplicate lines: <dup_line_count>");

	// Start from each duplicate and continue a block of 6 from other occurrences

}