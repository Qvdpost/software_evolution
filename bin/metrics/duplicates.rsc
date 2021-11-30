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

tuple[list[str], list[loc]] getBlock(loc src, map[list[str], set[list[loc]]] duplicates,  map[str, map[int, map[loc, str]]] locLines) {
	list[str] block = [locLines[src.path][src.begin.line][src]];
	list[loc] sources = [src];
	
	int fileLen = max(domain(locLines[src.path]));

	int line_number = src.begin.line;
	while (line_number < fileLen) {
		line_number += 1;
		
		if (line_number in locLines[src.path], lineLOC := locLines[src.path][line_number]) {
			for (tuple[loc src, str code] line <- toList(lineLOC)) {
				// Immediately terminate if the next LOC is not a duplicate.
				if ([line.code] notin duplicates) {
					return <block, sources>;
				}
				
				block += line.code;
				sources += line.src;
			}
		} 
	}
		
	return <block, sources>;
}

map[list[str], set[list[loc]]] getDuplicateBlock(tuple[list[str] code, list[loc] srcs] block, map[list[str], set[list[loc]]] duplicates) {
	int block_len = size(block.code);
	for (sub_block_size <- [0..block_len - 6 + 1], block_len >= 6) {
		for (block_size <- [6+sub_block_size..block_len+1]) {
			list[str] code_block = block.code[sub_block_size..block_size];
			list[loc] loc_block = block.srcs[sub_block_size..block_size];
							
			if (code_block notin duplicates)
				duplicates[code_block] = {loc_block};
			else
				duplicates[code_block] += {loc_block};
	
		}
	}
	return duplicates;
}

map[list[str], set[list[loc]]] getDuplicateBlocks(map[list[str], set[list[loc]]] duplicates, map[str, map[int, map[loc, str]]] locLines) {
	int file_count = size(locLines);
	for (file <- locLines, fileLOC := locLines[file]) {
		if (file_count % 100 == 0)
			println("Blocking <file> (<file_count> left)");
		file_count -= 1;
		
		int offset = 0;
		int fileLen = max(domain(fileLOC));
		
		for  (line_number <- [0..fileLen+1], line_number + offset < fileLen) {
			line_number += offset;
			if (line_number in fileLOC, lineLOC := fileLOC[line_number]) {
				for (src <- lineLOC, code := lineLOC[src], [code] in duplicates) {
					tuple[list[str] code, list[loc] srcs] block = getBlock(src, duplicates, locLines);
					int block_len = size(block.code);
					
					if (block_len >= 6) {
						duplicates = getDuplicateBlock(block, duplicates);
					}
					offset += block_len;
				}
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

map[list[str], set[loc]] filterSubsumption(map[list[str], set[loc]] duplicates) {

	map[loc, list[str]] duplicate_locs = ();
	map[str, map[loc, list[str]]] file_block_locs = ();
	
	println("Calculating locations");
	for (codeBlock <- duplicates) {
		for (block_loc <- duplicates[codeBlock]) {
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
			duplicates[duplicate_locs[block_loc]] -= block_loc;
		}
	}

	return duplicates;
}

void showDuplicateStats(map[list[str], set[loc]] duplicates, int code_count) {
	num dup_count = 0;
	num dup_line_count = 0;
	println("Calculating final duplicate blocks");
	for (codeBlock <- duplicates) {
		if (duplicates[codeBlock] != {}) {
			dup_count += size(duplicates[codeBlock]);
			dup_line_count += size(codeBlock) * size(duplicates[codeBlock]);
			println("Dup blocks @ <duplicates[codeBlock]>");
			println("");
		}
	}
	
	println("Total duplicates: <dup_count>");
	println("Total duplicate lines: <dup_line_count>");
	println("Duplicate percentage: <dup_line_count / code_count * 100>%");

}

map[list[str], set[loc]] getDuplicates(map[str, map[int, map[loc, str]]] locLines) {
	
	
	
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
	
	//num code_count = sum([size(domain(locLines[file])) | file <- locLines]);
	//showDuplicateStats(duplicate_blocks, code_count);
	
	return duplicate_blocks;
}