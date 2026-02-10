(* ::Package:: *)
(* search.wl : AQEI-bridge heuristic search (1+1 toy model)

   Stage III (Heuristic / Experimental)
   ----------------------------------
   This script searches over a finite-dimensional stress-energy ansatz space.

   What this does (heuristic):
   - Build N Gaussian wavepacket basis functions T_i(t,x).
   - Define an ad hoc family of M linear AQEI-like inequalities w_γ·a >= -B_γ.
   - Solve a linear program to maximize a causal-observable proxy Δ_
   (a)
     along several background "null" rays ℓ.

   What this is NOT (formal):
   - It is not a proof of any causal property in GR.
   - The observable Δ is an ansatz proxy, not an equivalence to reachability.

   Outputs:
   - mathematica/results/summary.json
   - mathematica/results/top_candidates.json

   Run:
     wolframscript -file mathematica/search.wl

   Environment knobs (optional):
     AQEI_NUM_BASIS (default 3)
     AQEI_NUM_CONSTRAINTS (default 12)
     AQEI_GRID (default 64)
     AQEI_DOMAIN (default 4.0)       (* domain is [-D,D] in both t and x *)
     AQEI_SIGMA (default 0.7)
     AQEI_SEED (default 1234)
     AQEI_EPS (default 1e-4)
     AQEI_A_MAX (default 1.0)
*)

ClearAll["Global`*"];

getEnvNumber[name_, default_] := Module[{s = Environment[name]},
  If[s === $Failed || s === None || s === "", default, ToExpression[s]]
];

(* Avoid protected symbols like N, D. *)
nBasis = Max[1, Floor@getEnvNumber["AQEI_NUM_BASIS", 3]];
nConstraints = Max[1, Floor@getEnvNumber["AQEI_NUM_CONSTRAINTS", 12]];
ngrid = Max[16, Floor@getEnvNumber["AQEI_GRID", 64]];
domainHalf = N@getEnvNumber["AQEI_DOMAIN", 4.0]; (* numeric half-width, i.e. [-D,D] *)
sigma = getEnvNumber["AQEI_SIGMA", 0.7];
seed = Floor@getEnvNumber["AQEI_SEED", 1234];
eps = getEnvNumber["AQEI_EPS", 1.*^-4];
aMax = getEnvNumber["AQEI_A_MAX", 1.0];

SeedRandom[seed];

resultsDir = FileNameJoin[{DirectoryName[$InputFileName], "results"}];
If[!DirectoryQ[resultsDir], CreateDirectory[resultsDir]];

(* Grid in (t,x) *)
ts = Subdivide[-domainHalf, domainHalf, ngrid - 1];
xs = Subdivide[-domainHalf, domainHalf, ngrid - 1];

(* Basis: Gaussian wavepackets (t,x) -> R *)
modes = Table[
  <|
    "kx" -> RandomReal[{0.5, 2.0}],
    "wt" -> RandomReal[{0.5, 2.0}],
    "phi" -> RandomReal[{-Pi, Pi}],
    "t0" -> RandomReal[{-1.0, 1.0}],
    "x0" -> RandomReal[{-1.0, 1.0}]
  |>,
  {i, nBasis}
];

gaussianMode[mode_, t_, x_] := Module[{kx, wt, phi, t0, x0},
  kx = mode["kx"]; wt = mode["wt"]; phi = mode["phi"]; t0 = mode["t0"]; x0 = mode["x0"];
  Exp[-((t - t0)^2 + (x - x0)^2)/(2 sigma^2)] * Cos[kx x + wt t + phi]
];

basisVals = Table[
  Table[gaussianMode[modes[[i]], t, x], {t, ts}, {x, xs}],
  {i, nBasis}
];

(* Fourier-domain Green multiplier for □h = S.
   We use a scalar toy multiplier: G(ω,k) = -1/(k^2 - ω^2 + eps).
   (Signature choice here is heuristic; eps regularizes near the lightcone.) *)

(* Frequency grid in the same ordering as Mathematica's `Fourier` output:
   0,1,2,...,N/2-1,-N/2,...,-1 (for even N). *)
freqGrid[n_] := Module[{half = Floor[n/2]},
  Join[Range[0, half - 1], Range[-half, -1]]
];

kgrid = 2 Pi * freqGrid[ngrid]/(2 domainHalf);

(* Build centered k arrays aligned with FourierShift conventions. *)
kt = kgrid;
kx = kgrid;

greenMultiplier[ω_, k_] := -1/(k^2 - ω^2 + eps);

applyGreen[b_] := Module[{Bhat, ωs, ks, mult, Hhat, h},
  (* 2D Fourier; we keep the native FFT ordering and match it in kgrid. *)
  Bhat = Fourier[b, FourierParameters -> {1, -1}];
  ωs = kt; ks = kx;
  mult = Table[greenMultiplier[ωs[[i]], ks[[j]]], {i, ngrid}, {j, ngrid}];
  Hhat = Bhat * mult;
  h = InverseFourier[Hhat, FourierParameters -> {1, -1}];
  (* Numerically, inverse transforms can carry tiny imaginary parts. *)
  N @ Chop[Re[h], 10^-12]
];

(* Observable proxy: integrate h(t,x) along approximate null rays.
   We use rays parameterized by λ in [-D,D]:
     ℓ+(λ) = (t=λ, x=λ)
     ℓ-(λ) = (t=λ, x=-λ)
   and two "tilted" rays as additional probes (heuristic).
*)
rays = {
  <|"name" -> "t=x", "vx" -> 1.0|>,
  <|"name" -> "t=-x", "vx" -> -1.0|>,
  <|"name" -> "t=0.5x", "vx" -> 0.5|>,
  <|"name" -> "t=-0.5x", "vx" -> -0.5|>
};

sampleField[h_, t_, x_] := Module[{ti, xi, tClamped, xClamped},
  tClamped = Clip[t, {-domainHalf, domainHalf}];
  xClamped = Clip[x, {-domainHalf, domainHalf}];
  ti = 1 + Round[(tClamped + domainHalf) (ngrid - 1)/(2 domainHalf)];
  xi = 1 + Round[(xClamped + domainHalf) (ngrid - 1)/(2 domainHalf)];
  h[[ti, xi]]
];

deltaAlongRay[h_, ray_] := Module[{vx, lambdas, vals},
  vx = ray["vx"];
  lambdas = ts; (* reuse grid for λ *)
  vals = Table[sampleField[h, λ, vx λ], {λ, lambdas}];
  (* Trapezoid integration in λ *)
  Total[Most[vals] + Rest[vals]] * (lambdas[[2]] - lambdas[[1]])/2
];

(* Precompute weights w_{i,j} = Δ(ray j, basis i) so Δ_j(a) = Sum_i a_i w_{i,j}. *)
weights = Table[
  Module[{hi = applyGreen[basisVals[[i]]]},
    Table[deltaAlongRay[hi, rays[[j]]], {j, Length[rays]}]
  ],
  {i, nBasis}
];

(* Synthetic AQEI constraints: wγ·a >= -Bγ.
   NOTE: these are placeholders; later versions should be derived from actual AQEI sampling.
*)
constraintNormals = Table[RandomReal[{-1, 1}, nBasis], {γ, nConstraints}];
constraintBounds = Table[RandomReal[{0.1, 1.0}], {γ, nConstraints}];

vars = Array[a, nBasis];

ineqs = Join[
  Table[constraintNormals[[γ]].vars >= -constraintBounds[[γ]], {γ, nConstraints}],
  Table[-aMax <= vars[[i]] <= aMax, {i, nBasis}]
];

(* Optimize each ray objective: maximize w_j·a subject to constraints. *)

optForRay[j_] := Module[{obj, sol, aStar, val, act, tol = 1.*^-6},
  obj = weights[[All, j]].vars;
  sol = Quiet@Check[
    LinearOptimization[-obj, ineqs, vars, {"PrimalMinimizer", "PrimalMinimumValue"}, Method -> "Simplex"],
    $Failed
  ];
  If[sol === $Failed || sol === {} || Length[sol] =!= 2, Return[$Failed]];
  (* In Wolfram 14.x, "PrimalMinimizer" is a numeric vector in the same order as `vars`. *)
  aStar = N @ sol[[1]];
  val = N @ (-sol[[2]]);
  (* Active constraints are those close to equality among the first nConstraints inequalities. *)
  act = Flatten@Position[
    Table[Abs[(constraintNormals[[γ]].aStar) - (-constraintBounds[[γ]])] <= tol, {γ, nConstraints}],
    True
  ];
  <|
    "rayIndex" -> j,
    "rayName" -> rays[[j]]["name"],
    "score" -> N@val,
    "a" -> N@aStar,
    "activeConstraints" -> act
  |>
];

cands = DeleteCases[Table[optForRay[j], {j, Length[rays]}], $Failed];

best = If[cands === {}, Null, First@SortBy[cands, -#score &]];

summary = <|
  "N" -> nBasis,
  "M" -> nConstraints,
  "grid" -> ngrid,
  "domain" -> domainHalf,
  "sigma" -> sigma,
  "seed" -> seed,
  "eps" -> eps,
  "aMax" -> aMax,
  "numRays" -> Length[rays],
  "best" -> best
|>;

Export[FileNameJoin[{resultsDir, "summary.json"}], summary, "JSON"];
Export[FileNameJoin[{resultsDir, "top_candidates.json"}], cands, "JSON"];

Print["Wrote: ", FileNameJoin[{resultsDir, "summary.json"}]];
Print["Wrote: ", FileNameJoin[{resultsDir, "top_candidates.json"}]];
