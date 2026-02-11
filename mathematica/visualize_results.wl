(* ::Package:: *)
(* visualize_results.wl

   Small Phase-3 helper: generate quick diagnostic plots from
   mathematica/results/*.json.

   This is intentionally minimal and test-friendly.

   Run:
     wolframscript -file mathematica/visualize_results.wl
     wolframscript -file mathematica/visualize_results.wl --test-mode
*)

ClearAll["Global`*"];

scriptArgs = If[ValueQ[$ScriptCommandLine], Rest[$ScriptCommandLine], {}];
testModeQ = MemberQ[scriptArgs, "--test-mode"] || Environment["AQEI_TEST_MODE"] === "1";

resultsDir = FileNameJoin[{DirectoryName[$InputFileName], "results"}];
summaryPath = FileNameJoin[{resultsDir, "summary.json"}];
candsPath = FileNameJoin[{resultsDir, "top_candidates.json"}];

If[!FileExistsQ[summaryPath] || !FileExistsQ[candsPath],
  Print["ERROR: expected results JSON files missing under: ", resultsDir];
  Quit[1];
];

summary = Import[summaryPath, "RawJSON"];
cands = Import[candsPath, "RawJSON"];

scores = If[ListQ[cands], Lookup[cands, "score", {}], {}];
labels = If[ListQ[cands], Lookup[cands, "rayName", {}], {}];

If[Length[scores] == 0,
  Print["No candidates in top_candidates.json; skipping plots."];
  Quit[0];
];

plot = BarChart[
  scores,
  ChartLabels -> Placed[labels, Below],
  PlotLabel -> "Candidate scores by ray",
  ImageSize -> 900
];

outPng = FileNameJoin[{resultsDir, If[testModeQ, "plot_scores_test.png", "plot_scores.png"]}];
Export[outPng, plot, "PNG"];

Print["Wrote: ", outPng];
