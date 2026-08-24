# R09 integrator request

The worker requests application of active shared-file request R0012 against exact C0006 code `fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`, followed by the normal
integrator-owned gates. The worker delivery itself contains none of these 0 shared paths.

Exact request evidence:

- request JSON: `D3B68F63F22D7D7A88A31F15D26A5FF07B2823AB6C74150EEC423052078FC3AC`
- sorted path list (0 paths): `06467703C117FE6C8A2D3F905DD4BF9E1B448E28E92C5456031721C7A88B359C`
- patch: `286035E05241C89BA3A5005BACBA1F20429B218381B44027D485E46AE1C5A9AE`
- postimage ledger: `BA8562218DBA95FD9F448B4D8F4557C726B7DB88E0A181599B772CD1883F2B67`
- reversible forward tree: `b13eee2c4e3f48013ea88ea47ffe5f108e3d6792`

## The 0 integrator-owned paths

0 declared shared paths:


0 consumer retargets, each of which only rewrites import lines that pointed at a historical owner:


On a disposable exact-base checkout, the integrator should replay R0012 forward, verify every postimage and the forward tree, replay it in reverse to the
exact base tree, apply it again, and overlay the worker delivery. The combined tree must have no canonical-destination reachability to a historical owner and
no reusable/internal reachability into `NumStability.Source`.

The remaining reviewed queue after R09 is exactly R10=18. Integration, acceptance, checkpoint state, main push, and branch
retirement remain primary-human/integrator controls and are not authorized by this request.

