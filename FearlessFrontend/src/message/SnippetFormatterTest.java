package message;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.net.URI;

import org.junit.jupiter.api.Test;

import files.Pos;

/**
 * Tests for SnippetFormatter (new contract):
 * - Code lines: "NNN|text" with NNN >= 3 digits, zero-padded.
 * - Caret / elision lines: spaces up to '|' column, then content (no "000").
 * - Multi-line: show start caret, optional middle (per maxMiddleLines), end caret.
 * - Context: configurable before/after.
 * - Span markers: [[...]] in input; end is INCLUSIVE.
 */
public class SnippetFormatterTest {

  private static final URI file= URI.create("mem:/Test.fear");

  /** Helper: takes (formatter, inputWithMarkers, expected) */
  private static void check(SnippetFormatter fmt, String input, String expected){
    int sIdx = input.indexOf("[[");
    int eIdx = input.indexOf("]]");
    if(sIdx < 0 || eIdx < 0 || eIdx < sIdx){ throw new IllegalArgumentException("Missing [[...]] markers"); }

    StringBuilder src = new StringBuilder(input.length() - 4);
    int line = 1, col = 1;
    int sLine = 1, sCol = 1, eLine = 1, eCol = 1;

    for(int i=0;i<input.length();){
      if(i == sIdx){
        sLine = line; sCol = col; i += 2; continue;
      }
      if(i == eIdx){
        eLine = line; eCol = Math.max(1, col - 1); i += 2; continue; // inclusive end
      }
      char c = input.charAt(i++);
      src.append(c);
      if(c == '\n'){ line++; col = 1; } else { col++; }
    }

    var span = Span.of(Pos.of(file, sLine, sCol), Pos.of(file, eLine, eCol));
    String out = fmt.caret(src.toString(), span);
    assertEquals(expected, out);
  }

  // -------------------- Tests (26) --------------------

  @Test
  public void t01_singleLine_middle_withUnderline(){
    check(
      SnippetFormatter.builder().build(),
      """
      one two three
      four [[five]] six
      seven eight nine
      """,
      """
      001|one two three
      002|four five six
         |     ^~~~
      003|seven eight nine
      """
    );
  }

  @Test
  public void t02_singleLine_emptySpan_pointCaret(){
    check(
      SnippetFormatter.builder().build(),
      """
      aaa bbb ccc
      ddd ee[[]]e fff
      ggg""",
      """
      001|aaa bbb ccc
      002|ddd eee fff
         |      ^
      003|ggg
      """
    );
  }

  @Test
  public void t03_singleLine_caret_at_col1(){
    check(
      SnippetFormatter.builder().build(),
      """
      L1
      [[X]]xxxxx
      L3
      """,
      """
      001|L1
      002|Xxxxxx
         |^
      003|L3
      """
    );
  }

  @Test
  public void t04_singleLine_caret_at_line_end(){
    check(
      SnippetFormatter.builder().build(),
      """
      pre
      end[[ ]]!//do multiline strings in java trim leading spaces?
      post
      """,
      """
      001|pre
      002|end !//do multiline strings in java trim leading spaces?
         |   ^
      003|post
      """
    );
  }

  @Test
  public void t05_twoAdjacentLines_noMiddle_noElision(){
    check(
      SnippetFormatter.builder().build(),
      """
      A
      [[b
      c]]
      D
      """,
      """
      001|A
      002|b
         |^
      003|c
         |^
      004|D
      """
    );
  }

  @Test
  public void t06_threeLines_oneMiddle_elided_by_default(){
    check(
      SnippetFormatter.builder().build(), // default maxMiddleLines=0 => elide
      """
      L1
      L2 [[start
      L3 middle
      L4 ]]end
      L5
      """,
      """
      001|L1
      002|L2 start
         |   ^
         |... 1 line ...
      004|L4 end
         |  ^
      005|L5
      """
    );
  }

  @Test
  public void t07_manyLines_elide_count_and_width_twoDigits(){
    check(
      SnippetFormatter.builder().build(),
      """
      L01
      L02
      L03 [[x
      L04
      L05
      L06
      L07
      L08
      L09
      L10
      L11
      L12
      L13
      L14
      L15
      L16
      L17
      L18 ]]y
      L19
      L20""",
      """
      002|L02
      003|L03 x
         |    ^
         |... 14 lines ...
      018|L18 y
         |   ^
      019|L19
      """
    );
  }

  @Test
  public void t08_noLineNumbers_singleLine(){
    check(
      SnippetFormatter.builder().showLineNumbers(false).build(),
      """
      one two three
      four [[five]] six
      seven eight nine
      """,
      """
      one two three
      four five six
           ^~~~
      seven eight nine
      """
    );
  }

  @Test
  public void t09_noLineNumbers_multiline_elision(){
    check(
      SnippetFormatter.builder().showLineNumbers(false).build(),
      """
      a
      b[[b
      c
      d]]d
      e
      """,
      """
      a
      bb
       ^
      ... 1 line ...
      dd
      ^
      e
      """
    );
  }

  @Test
  public void t10_tabExpansion_width4_singleLine(){
    check(
      SnippetFormatter.builder().tabWidth(4).build(),
      """
      \tfoo
      \tbar[[baz]]
      end""",
      """
      001|    foo
      002|    barbaz
         |       ^~~
      003|end
      """
    );
  }

  @Test
  public void t11_context_zero_zero(){
    check(
      SnippetFormatter.builder().contextBefore(0).contextAfter(0).build(),
      """
      a
      b [[c]] d
      e
      """,
      """
      002|b c d
         |  ^
      """
    );
  }

  @Test
  public void t12_context_two_one(){
    check(
      SnippetFormatter.builder().contextBefore(2).contextAfter(1).build(),
      """
      L1
      L2
      L3 [[here]] ok
      L4
      L5
      """,
      """
      001|L1
      002|L2
      003|L3 here ok
         |   ^~~~
      004|L4
      """
    );
  }

  @Test
  public void t13_show_two_middle_lines_no_elision(){
    check(
      SnippetFormatter.builder().maxMiddleLines(3).build(),
      """
      a
      [[b
      c
      d]]e
      f""",
      """
      001|a
      002|b
         |^
      003|c
      004|de
         |^
      005|f
      """
    );
  }

  @Test
  public void t14_elide_when_more_than_budget(){
    check(
      SnippetFormatter.builder().maxMiddleLines(1).build(),
      """
      a
      [[b
      c
      d
      e]]f""",
      """
      001|a
      002|b
         |^
         |... 2 lines ...
      005|ef
         |^
      """
    );
  }

  @Test
  public void t15_large_file_three_digits_confirm(){
    // 120 lines file; width must still be at least 3 digits (it is 3 by min) and numbers align.
    check(
      SnippetFormatter.builder().contextBefore(1).contextAfter(1).build(),
      // Build 118..122 with marker on 120 col 3 to 120 col 4
      """
      118
      119
      12[[0]]
      121
      122""",
      """
      002|119
      003|120
         |  ^
      004|121
      """
    );
  }

  @Test
  public void t16_singleLine_long_underline(){
    check(
      SnippetFormatter.builder().build(),
      """
      0123456789[[ABCDEFGHIJ]]K""",
      """
      001|0123456789ABCDEFGHIJK
         |          ^~~~~~~~~~
      """
    );
  }

  @Test
  public void t17_span_at_start_of_first_line(){
    check(
      SnippetFormatter.builder().build(),
      """
      [[ ]]start
      next
      """,
      """
      001| start
         |^
      002|next
      """
    );
  }

  @Test
  public void t18_span_at_end_of_last_line(){
    check(
      SnippetFormatter.builder().build(),
      """
      a
      last[[ ]]b""",
      """
      001|a
      002|last b
         |    ^
      """
    );
  }

  @Test
  public void t19_print_all_middle_lines_when_small(){
    check(
      SnippetFormatter.builder().maxMiddleLines(5).build(),
      """
      l1
      l2[[s
      m1
      m2
      m3]]e
      l8
      """,
      """
      001|l1
      002|l2s
         |  ^
      003|m1
      004|m2
      005|m3e
         | ^
      006|l8
      """
    );
  }

  @Test
  public void t20_no_line_numbers_multiline_no_elision(){
    check(
      SnippetFormatter.builder().showLineNumbers(false).maxMiddleLines(3).build(),
      """
      a
      [[b
      c
      d]]e""",
      """
      a
      b
      ^
      c
      de
      ^
      """
    );
  }

  @Test
  public void t21_middle_elision_count_pluralization(){
    check(
      SnippetFormatter.builder().build(),
      """
      L1
      [[L2
      L3
      L4
      L5]]L6""",
      """
      001|L1
      002|L2
         |^
         |... 2 lines ...
      005|L5L6
         | ^
      """
    );
  }

  @Test
  public void t22_tabExpansion_multiline(){
    check(
      SnippetFormatter.builder().tabWidth(4).build(),
      """
      \tA
      \tB[[b
      \tC
      \tD]]d""",
      """
      001|    A
      002|    Bb
         |     ^
         |... 1 line ...
      004|    Dd
         |    ^
      """
    );
  }

  @Test
  public void t23_context_zero_multiline_adjacent(){
    check(
      SnippetFormatter.builder().contextBefore(0).contextAfter(0).build(),
      """
      a
      [[b
      c]]d
      e
      """,
      """
      002|b
         |^
      003|cd
         |^
      """
    );
  }

  @Test
  public void t24_big_span_many_lines_elide_15plus(){
    check(
      SnippetFormatter.builder().build(),
      """
      L1
      L2 [[start
      L3
      L4
      L5
      L6
      L7
      L8
      L9
      L10
      L11
      L12
      L13
      L14
      L15
      L16
      L17
      L18
      L19
      L20]] end
      L21
      """,
      """
      001|L1
      002|L2 start
         |   ^
         |... 17 lines ...
      020|L20 end
         |  ^
      021|L21
      """
    );
  }

  @Test
  public void t24_big_span_many_lines_showAll(){
    check(
      SnippetFormatter.builder().maxMiddleLines(200).build(),
      """
      L1
      L2 [[start
      L3
      L4
      L5
      L6
      L7
      L8
      L9
      L10
      L11
      L12
      L13
      L14
      L15
      L16
      L17
      L18
      L19
      L20]] end
      L21
      """,
"""
001|L1
002|L2 start
   |   ^
003|L3
004|L4
005|L5
006|L6
007|L7
008|L8
009|L9
010|L10
011|L11
012|L12
013|L13
014|L14
015|L15
016|L16
017|L17
018|L18
019|L19
020|L20 end
   |  ^
021|L21
"""
    );
  }

  
  @Test
  public void t25_no_numbers_single_point_at_col1(){
    check(
      SnippetFormatter.builder().showLineNumbers(false).build(),
      """
      [[ ]]abc""",
      """
       abc
      ^
      """
    );
  }

  @Test
  public void t26_no_numbers_single_point_at_colN(){
    check(
      SnippetFormatter.builder().showLineNumbers(false).build(),
      """
      prefix[[ ]]X""",
      """
      prefix X
            ^
      """
    );
  }
}