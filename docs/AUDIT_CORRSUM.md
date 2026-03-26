# Audit Critique : Bug corrSum dans lean4_proof/

**Date** : 26 mars 2026  
**Sévérité** : CRITIQUE — affecte lean4_proof/ et l'article.  
**Ne touche PAS** : lean/verified/ ni lean/skeleton/ (formule correcte).

## Le bug

Le repo lean4_proof/ (Range Exclusion) calcule :

    corrSum_RE(A, k) = Σ 3^{k-1-i} · 2^{A[i]}

où A vient de `enumMonotone` (partitions non-décroissantes sommant à S).

La formule correcte de Steiner est :

    corrSum_Steiner(k, A) = Σ 3^{k-1-i} · 2^{A_i}

où A = (0, A_1, ..., A_{k-1}) sont les **positions cumulatives** strictement croissantes avec A_0 = 0 et A_i < S, générées par `compList(S, k)` dans lean/verified/.

**Preuve du bug** : pour k=2, le cycle trivial n₁=1 a gaps=(2,2), positions A=(0,2).
- corrSum_Steiner = 3·1 + 1·4 = 7 = d → n₁ = 1. ✅ Détecte le cycle.
- corrSum_RE([2,2], 2) = 3·4 + 1·4 = 16. 16 mod 7 = 2 ≠ 0. ❌ Ne détecte pas.

## Ce qui est correct

| Composant | Formule | Domaine | Verdict |
|-----------|---------|---------|---------|
| lean/skeleton/ (JunctionTheorem.lean) | Σ 3^{k-1-i}·2^{A_i} | Positions A(0)=0 < A(1) < ... < S | ✅ CORRECT |
| lean/verified/ (280 théorèmes) | corrSumList, compList=enumIncr | Positions strictement croissantes | ✅ CORRECT |
| lean4_proof/ (Range Exclusion) | corrSumGo, enumMonotone | Partitions non-décroissantes | ❌ FAUX |
| article V2 eq.(3) | Σ 3^{k-j}·2^{tail_j} | Tail sums g_{j+1}+...+g_k | ❌ FAUX |

## N₀ avec la bonne formule

Calculé exhaustivement avec corrSum_Steiner (positions) :

| k | S | d | C(S-1,k-1) | N₀ |
|---|---|---|------------|-----|
| 3 | 5 | 5 | 6 | **0** |
| 4 | 7 | 47 | 20 | **0** |
| 5 | 8 | 13 | 35 | **0** |
| 6 | 10 | 295 | 126 | **0** |
| ... | ... | ... | ... | **0** |
| 15 | 24 | 2428309 | 817190 | **0** |
| 16 | 26 | 24062143 | 3268760 | **0** |
| 17 | 27 | 5077565 | 5311735 | **0** |
| 18 | 29 | 149450423 | 21474180 | **0** |

N₀ = 0 pour **tout** k = 3..18 (bonne formule, calcul exhaustif Python).

N₀ = 0 pour k = 3..15 est **prouvé en Lean** (lean/verified/, 280 théorèmes, 0 sorry).

## Ce qui est prouvé (claim honnête)

1. **N₀(d) = 0 pour k = 3..15** — Lean verified, bonne formule, 0 sorry, 0 axiom.
2. **N₀(d) = 0 pour k = 16..18** — Python exhaustif, bonne formule (non formalisé en Lean).
3. **Pas de cycle pour k ≤ 91** — Hercher (2025), résultat publié.
4. **C(S-1,k-1) < d pour k ≥ 18** — nonsurjectivité, prouvée dans lean/skeleton/.
5. **Spectral gap ρ_p < 1** — Wielandt, pour tout p > 3 (PROMETHEUS).

## Ce qui n'est PAS prouvé

- N₀(d) = 0 pour k > 18 n'est pas établi formellement.
- Le lean4_proof/ (Range Exclusion) ne prouve rien sur les vrais cycles de Collatz.
- L'argument Baker pour k ≥ 10001 s'applique à la mauvaise fonction.
- Le gap entre « C < d » (nonsurjectivité) et « N₀ = 0 » reste ouvert pour k > 91.

## Impact sur le repo de publication

Le repo `collatz-cycles-lean` doit être mis à jour :
1. Retirer lean4_proof/ du chemin de preuve principal (le garder avec un WARNING)
2. Corriger l'article : formule corrSum, claim réduit
3. Clarifier que la preuve formelle couvre k ≤ 15, Hercher couvre k ≤ 91

## Pourquoi lean/verified/ est correct

Le fichier `lean/verified/CollatzVerified/Basic.lean` définit :
- `compList(S, k)` = `(enumIncr(k-1, 1, S-1)).map (0 :: ·)` — positions strictement croissantes
- `corrSumList(positions)` = Σ 3^{k-1-i} · 2^{positions[i]} — formule de Steiner

Ces 280 théorèmes sont **indépendants** de lean4_proof/ et utilisent la **bonne** formule.
