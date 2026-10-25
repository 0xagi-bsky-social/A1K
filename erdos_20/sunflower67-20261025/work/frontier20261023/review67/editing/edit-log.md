# Spacing and mathematical notation edit log

This is a production copy edit of `public/round01/manuscript.md`, not a specialist review or a mathematical approval. The original file is unchanged. The complete edited copy is `editing/spacing-math.md`. No incoming or pending reviewer material was inspected.

Policy: restore missing spaces between prose and numerals, within dates, after commas and around mathematical operators; retain named objects such as P10, Q8 and H27, suite names, source commits, URLs and companion filenames. Replace the set-difference backslash with Unicode ∖. Represent originally underscored indices by square brackets, including the whole index expression, and add one explicit notation sentence distinguishing N[R]. Remove four-space equation indentation so equations remain ordinary Markdown paragraphs. All scientific words, facts and formula contents are preserved modulo those declared notation substitutions and whitespace.

Detected and resolved during editing: the first draft incorrectly inserted spaces inside the commit and version suffixes; its boundary-based commit test matched zero source occurrences. The final pass protects the literal commit and versioned archive identifiers, restores their exact spelling, and checks actual occurrence counts. Visual source inspection also caught operator spacing inside C++; the language name is restored, protected and checked as one exact occurrence.

Renderer inspection: `/home/user/.codex/skills/superresearch-x2/scripts/native_publication.py` uses CommonMark with tables and has optional math spans. Its `math_renderer.py` requires macros for several raw Unicode operators. This copy therefore uses plain Unicode mathematics and explicitly grouped indices. Only a CommonMark parse was run; no HTML, PDF or publication artifact was generated.

Checks actually performed on the written copy:

- After removing the single notation sentence, replacing only the declared index/set-difference notation and stripping whitespace, the complete edited content is character-for-character identical to the source. This checks all scientific text and formula symbols, not merely selected numbers.
- The complete ordered sequence of digit runs is identical, including dates, counts, bounds, indices and source identifiers.
- Ordered URL, versioned archive identifier, companion-filename and named-object sequences are identical. The exact known forty-hex commit `90c03c79bcf44eb8f61dff1b86091b822cc4cd3c` occurs twice in both files; this check requires two actual occurrences and does not rely on a missing source word boundary.
- The original source bytes are unchanged; SHA-256 commitments are recorded below.
- CommonMark parsing finds no code blocks, fences or underscore-generated emphasis. No mathematical underscore indices or backslashes remain.

```json
{
  "source_sha256": "2c200bf5dff9e665e7dab3ba3f5a1ef019251d341a1913d1f5bd2fc3c086f937",
  "edited_sha256": "7a0f3208c747df4befeaf6040f0b8119092a0adf170ffea0d930d12d2dd8f100",
  "ordered_digit_runs_preserved": 647,
  "URLs_preserved": 6,
  "exact_known_commit_occurrences_preserved": 2,
  "versioned_archive_identifiers_preserved": 7,
  "companion_filenames_preserved": 12,
  "paragraphs_original": 100,
  "paragraphs_edited": 101,
  "source_unchanged": true,
  "declared_notation_and_whitespace_canonical_check": "identical",
  "exact_C_plus_plus_literal_occurrences_preserved": 1,
  "code_blocks_parsed": 0,
  "underscore_emphasis_pairs_parsed": 0
}
```
