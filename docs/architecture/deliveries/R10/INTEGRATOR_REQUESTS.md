# R10 integrator request

The worker requests application of active shared-file request R0013 against exact C0006 code `fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`, followed by the normal
integrator-owned gates. The worker delivery itself contains none of these 0 shared paths.

Exact request evidence:

- request JSON: `4EFC8B59FEEBFD1A3D9EBDDAD471A6A3FD4C5C113EBC4652BBC8092061ABFD38`
- sorted path list (0 paths): `DD502BA5AAEC5C37CC0E3762EDD09AF3614ADCFC90589FAA5F32D6374BFCDF9A`
- patch: `1C716FF5B10C4907BE42F9139A99906B11F616A5512EB10CFBCCD767A77A4ECE`
- postimage ledger: `3AECB34386A4CDC11A429D463FE8A74073B3A09E7678E06A2107350C646D06D2`
- reversible forward tree: `4483687515e9c751d4d3978daeabdcb8d994e007`

## The 0 integrator-owned paths

0 declared shared paths:


0 consumer retargets, each of which only rewrites import lines that pointed at a historical owner:


On a disposable exact-base checkout, the integrator should replay R0013 forward, verify every postimage and the forward tree, replay it in reverse to the
exact base tree, apply it again, and overlay the worker delivery. The combined tree must have no canonical-destination reachability to a historical owner and
no reusable/internal reachability into `NumStability.Source`.

The remaining reviewed queue after R10 is exactly R10=18. Integration, acceptance, checkpoint state, main push, and branch
retirement remain primary-human/integrator controls and are not authorized by this request.

