
import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.IntStream;

import javax.xml.parsers.ParserConfigurationException;

import edu.unl.cse.iotcom.AlloySolver;
import edu.unl.cse.iotcom.AlloySolver.SolverResult;
import freemarker.template.Template;

import edu.mit.csail.sdg.alloy4compiler.translator.*;
import edu.mit.csail.sdg.alloy4.Err;

public class SandBoxSolver {

	private static int limit = 10;

	
	public static Map<String, List<String>> readLinkFile(String pathToLinkFile) throws IOException {
		
		Map<String, List<String>> result = new HashMap<>();
		
		String linkFileContent = new String(Files.readAllBytes(Paths.get(pathToLinkFile)));
		for (String line : linkFileContent.split("\n") ) {
			
			if (!line.contains("_trig")) {
				continue;
			}
			
			String name = line.split(",")[0].split("_trig")[0];
			String attr = line.split(",")[1];
			String value = line.split(",")[2];
			
			
			// only triggers interest me for now...
			result.put(name, new ArrayList<>());
			result.get(name).add(attr);
			result.get(name).add(value);
		}
		
		return result;
	}
	
	public static void main(String... args) {

		try {
			int bundleSize = 0;
			String pathToStage = args[0];
			
			String pathToLinkFile = args[1];

			System.out.println("path to stage directory: " + pathToStage);
			System.out.println("path to link file: " + pathToLinkFile);
			
			
			File stageDir = new File(pathToStage);

			String bundleFileContent = "";
			String newAssertions = "";
			for (File f : stageDir.listFiles()) {
				boolean isApp = f.toString().contains("app_");
				if (isApp) {
					bundleSize += 1;
					continue;
				}

				boolean isBundle = f.toString().contains("bundle-");
				if (isBundle) {
					bundleFileContent = new String(Files.readAllBytes(f.toPath()));
				}

				boolean isNewAssertionsFile = f.toString().contains("assertions_") && !f.toString().contains(".bak");
				if (isNewAssertionsFile) {
					newAssertions = new String(Files.readAllBytes(f.toPath()));
				}
			}
			
			
			// read links
			Map<String, List<String>> ruleNameLinksToAttrVal = readLinkFile(pathToLinkFile);
			
//			bundleFileContent += "\n" + newAssertions;

			Map<String, List<String>> propertyToPairs = new HashMap<>();
			List<String> propertyList = new ArrayList<>();
			
			String presentCommandAttribute = "";
			String presentCommandValue = "";
			for (String line : newAssertions.split("\n")) {
				if (line.contains("check ")) {
					propertyList.add(line.split("check")[1].trim());
				}
				if (line.startsWith("//") && line.contains(":cap") && line.contains(",")) { // probably one the lines
																							// used to asosciate the
																							// rule and the
																							// attribute,value pairs
					String propertyName = line.split("//")[1].split(":")[0].trim();
//					String[] names = line.split("//")[1].split(":")[1].split(",");
//					String commandAttribute = names[0];
//					String commandValue = names[1];
//					String interestingAttribute = names[2];
//					String interestingValue = names[3];
					
					// the stuff without the command name
					String lineContent = line.split("//")[1].split(":")[1].trim();
					presentCommandAttribute = lineContent.split(",")[0];
					presentCommandValue = lineContent.split(",")[1];
					
					propertyToPairs.put(propertyName, new ArrayList<>());
					propertyToPairs.get(propertyName).add(line.split("//")[1].split(":")[1].trim());
				}
				
				if (line.startsWith("//") && line.contains(":^,cap") && line.contains(",")) { 
					String propertyName = line.split("//")[1].split(":")[0].trim();
					
					String lineContent = line.split("//")[1].split(":\\^,")[1].trim();
					propertyToPairs.get(propertyName).add(
							presentCommandAttribute + "," + presentCommandValue + "," + lineContent);
					System.out.println("\tadding updated assertion" + presentCommandAttribute + "," + presentCommandValue + "," + lineContent);
				}
			}

			
			
			File sandBoxTestFile = new File(pathToStage + "/sandbox.als");
			Files.write(sandBoxTestFile.toPath(), newAssertions.getBytes());

			System.out.println("Written to file");

			final AlloySolver solver = new AlloySolver(stageDir, limit, null);
//			System.out.println("Running Alloy");
			Map<String, Map.Entry<SolverResult, Map<String, List<String>>>> solutions = solver.getSolutionsForFileForSandBox(sandBoxTestFile,
					propertyList);
			System.out.println("Done Running Alloy. Size = " + solutions.size());

			
			List<String> assertionUpdates = new ArrayList<>();
			
			long time = 0;
			List<String> potentiallyHolds = new ArrayList<>();
			for (Map.Entry<String, Map.Entry<SolverResult, Map<String, List<String>>>> r : solutions.entrySet()) {
				final AlloySolver.SolverResult value = r.getValue().getKey();
				Map<String, List<String>> commandSkolemBindings = r.getValue().getValue();

				boolean hasCounterExample = value.getCounterExampleCount() > 0;
				
				if (hasCounterExample) {
					System.out.println(r.getKey() + " has counterexample");
//					System.out.println(r.getKey().split(",")[0]);
//					System.out.println(commandSkolemBindings);
					List<String> ruleNames = commandSkolemBindings.get(r.getKey().split(",")[0]);
					System.out.println("add r=" + ruleNames );
					
					
					for (String ruleName : ruleNames) {
						System.out.println(ruleNameLinksToAttrVal.get(ruleName));
						assertionUpdates.add(r.getKey().split(",")[0] + "," + String.join(",", ruleNameLinksToAttrVal.get(ruleName)).trim() + "\n");
					}
					
				} else {
					System.out.println(r.getKey() + " has no counterexample and may hold");
					potentiallyHolds.add(r.getKey().split(",")[0]);
				}
				long solveTime = value.getSolveTimeMS();
				time += solveTime;
			}

			Collections.sort(potentiallyHolds);
			
			List<String> result = new ArrayList<>();
			for (String property : potentiallyHolds) {
				List<String> pairs = propertyToPairs.get(property);
				for (String pair : pairs) {
					result.add(pair);
				}
			}
			
			
			Collections.sort(result);
		
			File outputFile = new File(pathToStage + "/holdPairs.txt");
			Files.write(outputFile.toPath(), String.join("\n", result).getBytes());
			System.out.println("pairs are stored at " + outputFile);
			
			outputFile = new File(pathToStage + "/newAssertions.txt");
			Files.write(outputFile.toPath(), String.join("", assertionUpdates).getBytes());
			System.out.println("new assertions are stored at " + outputFile);
			
			System.out.println("trace the paths using the python script: complete_hold_pairs.py");
			System.out.println("time needed (in ms)");
			System.out.println(time);
			
			
		} catch (IOException | Err e) {
			System.err.println("oh my");
			throw new RuntimeException(e);
		}
	}
	
	static void getEventAttributeAndValueFrom(String appFileContent) {
		for (String line : appFileContent.split("\n")) {
			
			
		}
		
	}
	

	private static BufferedWriter appendWriter(Path path) throws IOException {
		return Files.newBufferedWriter(path, StandardOpenOption.CREATE, StandardOpenOption.APPEND);
	}

}
