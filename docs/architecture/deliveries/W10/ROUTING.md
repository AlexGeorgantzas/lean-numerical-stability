# W10 routing

All 1,029 declarations selected from the 27 C0007 owners have a declaration-level reviewed
route. Frozen tier suggestions were review inputs, not executable classifications.

| quantity | value |
| --- | ---: |
| retained at owners | 134 |
| relocated | 895 |
| reusable | 494 |
| Chapter 15 source | 401 |
| actual physical reusable modules | 49 |
| actual physical source declaration modules | 46 |
| declaration-free Source correspondence wrappers | 1 |
| authorized destination prefixes populated | 43 of 43 |

`DECLARATION_ROUTES.tsv.destination_module` names the exact module that contains the
declaration in the full format-2 candidate. `CHECK_STATIC.py` derives this mapping directly
from the candidate and rejects missing, duplicate, coarse-prefix, nonexistent, or tier-
inconsistent routes. The other fields retain the semantic review decision:

- reusable means generic norm or condition-estimation mathematics;
- source means exact Chapter 15 correspondence;
- historical means retained at its exact owner: either a member of the 132-name private
  reverse closure or one of the two reviewed full-graph re-entry hazards;
- `demoted=yes` records one of the 22 declarations moved from a preliminary reusable
  suggestion to source to close an induced-graph dependency.

The tier fixpoint took five passes and 22 demotions. It eliminates all in-wave reusable-to-
source declaration edges without misclassifying printed endpoints as reusable. The final
physical production graph has zero reusable-to-Source reachability and no import cycles.

The generic `cond_norm_identity` and `oneNorm_eq_infNorm_transpose'` declarations were
rerouted from the preliminary Source suggestion into the existing reusable finite-index
leaf. The Source path remains as a declaration-free correspondence wrapper, and
`Algorithms.CondEstimation` is source-neutral reusable-in-place. Therefore accepted
consumer and historical-root imports are preserved, while both the worker and the exact
14-path integrator postimages have zero reusable-to-Source and canonical-to-historical
reachability.
