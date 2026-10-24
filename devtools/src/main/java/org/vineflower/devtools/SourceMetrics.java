package org.vineflower.devtools;

/**
 * Counts double casts in printed source: a parenthesised type whose operand is another cast.
 *
 * <p>javac reports redundant single casts through {@code -Xlint:cast} but has no warning for a
 * double cast, so this shape needs its own text matcher. The scan skips comments and literals and
 * refuses a parenthesis that follows an expression, which is a call or a group. This is a
 * measurement, not a parse: it is used to compare trees, never to decide a rewrite.
 */
public final class SourceMetrics {
  public record Counts(int doubleCasts) {
    public static final Counts ZERO = new Counts(0);

    public Counts plus(Counts other) {
      return new Counts(doubleCasts + other.doubleCasts);
    }
  }

  private SourceMetrics() {
  }

  public static Counts casts(String text) {
    int doubleCasts = 0;
    int n = text.length();
    int previous = -1;
    int i = 0;
    while (i < n) {
      char c = text.charAt(i);
      if (c == '/' && i + 1 < n && text.charAt(i + 1) == '/') {
        int end = text.indexOf('\n', i);
        i = end < 0 ? n : end + 1;
        continue;
      }
      if (c == '/' && i + 1 < n && text.charAt(i + 1) == '*') {
        int end = text.indexOf("*/", i + 2);
        i = end < 0 ? n : end + 2;
        continue;
      }
      if (c == '"') {
        if (text.startsWith("\"\"\"", i)) {
          int end = text.indexOf("\"\"\"", i + 3);
          i = end < 0 ? n : end + 3;
        }
        else {
          i = quotedEnd(text, i, '"');
        }
        previous = i - 1;
        continue;
      }
      if (c == '\'') {
        i = quotedEnd(text, i, '\'');
        previous = i - 1;
        continue;
      }
      if (c == '(') {
        int close = matchingParen(text, i);
        if (close > i) {
          boolean afterExpression = previous >= 0 && endsExpression(text, previous)
            && !keywordBefore(text, previous);
          if (!afterExpression && looksLikeType(text, i + 1, close)) {
            int operand = skipSpace(text, close + 1);
            if (operand < n && startsOperand(text.charAt(operand))) {
              if (text.charAt(operand) == '(') {
                int innerClose = matchingParen(text, operand);
                if (innerClose > operand && looksLikeType(text, operand + 1, innerClose)) {
                  int innerOperand = skipSpace(text, innerClose + 1);
                  if (innerOperand < n && startsOperand(text.charAt(innerOperand))) {
                    doubleCasts++;
                  }
                }
              }
              previous = close;
              i = close + 1; // the operand is scanned from its own first character
              continue;
            }
          }
          // A call or a group: its contents are scanned normally, so casts in an argument list
          // are still seen.
          previous = i;
          i++;
          continue;
        }
      }
      if (!Character.isWhitespace(c)) {
        previous = i;
      }
      i++;
    }
    return new Counts(doubleCasts);
  }

  private static int quotedEnd(String text, int start, char quote) {
    int i = start + 1;
    while (i < text.length()) {
      char c = text.charAt(i);
      if (c == '\\') {
        i += 2;
        continue;
      }
      if (c == quote) {
        return i + 1;
      }
      i++;
    }
    return text.length();
  }

  private static int matchingParen(String text, int open) {
    int depth = 0;
    int i = open;
    while (i < text.length()) {
      char c = text.charAt(i);
      if (c == '"') {
        if (text.startsWith("\"\"\"", i)) {
          int end = text.indexOf("\"\"\"", i + 3);
          i = end < 0 ? text.length() : end + 3;
        }
        else {
          i = quotedEnd(text, i, '"');
        }
        continue;
      }
      if (c == '\'') {
        i = quotedEnd(text, i, '\'');
        continue;
      }
      if (c == '/' && i + 1 < text.length() && text.charAt(i + 1) == '/') {
        int end = text.indexOf('\n', i);
        i = end < 0 ? text.length() : end + 1;
        continue;
      }
      if (c == '/' && i + 1 < text.length() && text.charAt(i + 1) == '*') {
        int end = text.indexOf("*/", i + 2);
        i = end < 0 ? text.length() : end + 2;
        continue;
      }
      if (c == '(') {
        depth++;
      }
      else if (c == ')') {
        depth--;
        if (depth == 0) {
          return i;
        }
      }
      i++;
    }
    return -1;
  }

  private static int skipSpace(String text, int i) {
    while (i < text.length() && Character.isWhitespace(text.charAt(i))) {
      i++;
    }
    return i;
  }

  private static boolean endsExpression(String text, int at) {
    char c = text.charAt(at);
    return Character.isLetterOrDigit(c) || c == '_' || c == ')' || c == ']' || c == '.' || c == '>';
  }

  private static boolean keywordBefore(String text, int at) {
    int start = at;
    while (start >= 0 && (Character.isLetterOrDigit(text.charAt(start)) || text.charAt(start) == '_')) {
      start--;
    }
    String word = text.substring(start + 1, at + 1);
    return switch (word) {
      case "return", "throw", "case", "else", "yield", "assert", "do" -> true;
      default -> false;
    };
  }

  private static boolean startsOperand(char c) {
    return Character.isLetterOrDigit(c) || c == '_' || c == '$' || c == '(' || c == '!'
      || c == '~' || c == '-' || c == '+' || c == '@';
  }

  private static boolean looksLikeType(String text, int from, int to) {
    String content = text.substring(from, to).trim();
    if (content.isEmpty()) {
      return false;
    }
    for (int i = 0; i < content.length(); i++) {
      char c = content.charAt(i);
      if (Character.isLetterOrDigit(c) || c == '_' || c == '$' || c == '.' || c == '<' || c == '>'
        || c == ',' || c == '?' || c == '[' || c == ']' || c == '&' || c == ' '
        || c == '@' || c == '*') {
        continue;
      }
      return false;
    }
    char first = content.charAt(0);
    if (!Character.isJavaIdentifierStart(first) && first != '?' && first != '@') {
      return false;
    }
    // A single lower-case identifier is far more often a parenthesised variable than a cast; every
    // primitive and the type keywords are accepted explicitly instead.
    String head = content.split("[<\\[\\s]", 2)[0];
    if (head.indexOf('.') < 0 && !head.equals("int") && !head.equals("long") && !head.equals("short")
        && !head.equals("byte") && !head.equals("char") && !head.equals("boolean")
        && !head.equals("float") && !head.equals("double") && !head.equals("var")) {
      if (!Character.isUpperCase(head.charAt(0))) {
        return false;
      }
    }
    return !content.equals("new") && !content.startsWith("new ");
  }
}
