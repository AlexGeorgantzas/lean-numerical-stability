# NumStability documentation

This release branch retains only the documentation needed to discover and
import the installed library. Internal architecture, migration, benchmarking,
and source-audit records remain on the development branches.

## Library discovery

- [`LIBRARY_LOOKUP.md`](LIBRARY_LOOKUP.md) is the human-readable, structure-first
  map. It tells users and agents which subtree owns each kind of declaration,
  lists the main domain imports, and indexes every Higham chapter.
- [`../examples/LibraryLookup.lean`](../examples/LibraryLookup.lean) is the
  executable companion. Its narrow imports and representative `#check`
  commands verify that the documented navigation paths still work.

The lookup is curated for fast discovery rather than generated as an exhaustive
declaration dump. For an exact declaration owner, use `rg` in the indicated
subtree and confirm the narrow import with Lean.
