# Pilot 29 Titan reboot incident

At the last reachable read around 2026-09-24 02:40 UTC, Pilot 29 was
`RUNNING_PARALLEL`: five pairs sealed, three pairs active, and two unstarted.
SSH then timed out. Titan became reachable again at the same public IP on
2026-09-24. Its boot time was 2026-09-24 07:37:38, and neither the campaign
controller nor any pair-lane process survived. The journal still says
`RUNNING_PARALLEL`; this is stale process state, **not** a completed campaign.

Read-only inspection found campaign input identity
`59a816765dc398f2bb49eb7fca71e773c116edd6efb63fbfb55609e404f044c4`
and campaign JSON SHA-256
`423bf0fe15961a0d731662a8927f21454d6792997cab2feb99a8a4186c05ca62`.
The five journal-sealed pair-report hashes still match their recorded hashes:

| Task | Preserved status |
| --- | --- |
| CAST08-FIXED3 | Both statements faithful; both proved |
| RUMP12-THM3.4 | Both statements faithful; both proved |
| FAB19-EQ3.6 | Both statements faithful; neither proved within four submissions |
| CAST08-PROP3.2 | Both statements faithful; both proved |
| H20-8 | Both statements faithful; both proved |

The partial `RUNNING` pair reports were LL07-THM4
(`56b548af919c12dea183feac00e05f6f397130f67f8faa785b5ec9fe6dcd5211`),
RUMP12-THM3.5
(`3f6d0da5821829e4b79cc341bafedc7a8eaf871c4409e4541b169264037bb842`),
and CAST08-PROP3.1
(`39711deb05721853dbe9a8a52e11a439350ceae41c23162c0c05ae68f032bdc1`).
These hashes identify last-written partial reports only. LL07-THM7 and
FAB19-EQ3.5 had no pair directory. There is no supported in-place resume:
`design22_campaign.py` accepts resumption only from `PAUSED_FIRST_REVIEW`,
while `design20_matched.py` rejects an existing pair output root. Pilot 29
must not be reclassified as complete, and no interrupted pair may be silently
restarted under its identity.
