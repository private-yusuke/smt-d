module smtd.app;

import smtd.smt_solver : SExpression, SMTSolver;
import smtd.util.constants;
import std.stdio : stdin, writeln, File;
import std.file : readText;
import std.range : front, array, join;
import std.getopt;
import std.typecons : Yes;
import std.conv : to;

/// テスト用の入力
const auto content = `(set-logic QF_UF)
(set-option :produce-models true)
(set-info :category "crafted")
(set-info :keyword |
test|)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (< a b))
(assert (> a b))
(assert (<= a b))
(assert (>= a b))
(check-sat)
`;

struct CommandLineOptions
{
	string filePath;
	bool generateCongruenceClosureGraph;
	string congruenceClosureGraphs;
}

// unittest に silly を利用する都合で、unittest のためにビルドするときにはここの main 関数を消す
version (unittest)
{
}
else
{
	int main(string[] args)
	{
		CommandLineOptions options;
		auto helpInformation = getopt(args, "file|f",
				"path to SMT-LIB2 input file", &options.filePath,
				"generate-congruence-closure-graph", "generate DOT files representing graphs of Congruence Closure Algorithm", &options.generateCongruenceClosureGraph,
				"congruence-closure-graphs-destination", "manually specify path to destination directory of DOT files representing graphs of Congruence Closure Algorithm", &options.congruenceClosureGraphs);

		if (helpInformation.helpWanted)
		{
			defaultGetoptPrinter("smt-d solves problems written in SMT-LIBv2 language.",
					helpInformation.options);
			return 0;
		}

		auto solver = new SMTSolver();

		import smtd.expression : StringExpression;

		if (options.generateCongruenceClosureGraph) {
			solver.setInfo(GENERATE_CONGRUENCE_CLOSURE_GRAPH_INFO , new StringExpression("true"));
		}

		if (options.congruenceClosureGraphs) {
			solver.setInfo(CONGRUENCE_CLOSURE_GRAPH_DESTINATION_INFO, new StringExpression(options.congruenceClosureGraphs));
		}

		File file = options.filePath ? File(options.filePath) : stdin;

		string getInputFileName(File file) {
			string filename = file.name;

			if (filename) {
				return filename;
			}
			import std.datetime.systime : Clock;
			return "input_" ~ Clock.currTime().toISOExtString;
		}

		solver.setInfo(INPUT_FILE_NAME_INFO, new StringExpression(getInputFileName(file)));

		auto parsedTree = parseInput(file);
		foreach (sExpr; parsedTree.children.front.children)
		{
			auto expr = solver.parseTree(sExpr);
			solver.runExpression(expr);
		}
		return 0;
	}

	/**
	 * 与えられたファイルの内容を読み取り、Pegged で提供されているパーサーに入力を与えた結果を返します。
	 */
	auto parseInput(File f = stdin)
	{
		string content = f.byLineCopy(Yes.keepTerminator).join.array.to!string;
		return SExpression(content);
	}
}
