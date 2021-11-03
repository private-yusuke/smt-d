module smtd.app;

import smtd.smt_solver : SExpression, SMTSolver;
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
				"path to SMT-LIB2 input file", &options.filePath);

		if (helpInformation.helpWanted)
		{
			defaultGetoptPrinter("smt-d solves problems written in SMT-LIBv2 language.",
					helpInformation.options);
			return 1;
		}

		auto solver = new SMTSolver();

		File file = options.filePath ? File(options.filePath) : stdin;
		auto parsedTree = parseInput(file);
		foreach (sExpr; parsedTree.children.front.children)
		{
			auto expr = solver.parseTree(sExpr);
			solver.runExpression(expr);
		}

		solver.getStatusString().writeln;
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
