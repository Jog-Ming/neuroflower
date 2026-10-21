// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.main;

import org.jetbrains.java.decompiler.code.CodeConstants;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructField;
import org.jetbrains.java.decompiler.struct.attr.StructConstantValueAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.consts.LinkConstant;
import org.jetbrains.java.decompiler.struct.consts.PooledConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Restores references to inlined constants from the constant pool.
 *
 * <p>javac enters a class into the pool when the source names one of its constants, even though the
 * constant itself is folded to a literal. So a class the jar's pool holds and this file's text never
 * mentions is trace evidence that the original wrote {@code Owner.NAME} at some literal. The literal
 * is rewritten only when exactly one such missing owner declares that value, and the printed form is
 * valid source; nothing is compiled, so an ambiguous value is left alone.
 */
public final class ConstantNames {
  private ConstantNames() {
  }

  private record Constant(String owner, String name, VariableType kind) {
  }

  private enum VariableType {
    INT, LONG, FLOAT, DOUBLE, STRING, BOOLEAN, CHAR
  }

  private record Site(int start, int end, String replacement) {
  }

  /** The text with named constants restored, or the same text when nothing is provable. */
  public static String restore(String text, ClassNode root) {
    Set<String> present = new LinkedHashSet<>();
    Set<String> referenced = new LinkedHashSet<>();
    collectPool(root, present, referenced);
    Set<String> missing = new LinkedHashSet<>();
    for (String owner : present) {
      String simple = simpleName(owner);
      // A class the pool references through a field or method is already in the pool for that
      // reason; its presence is no evidence that the source named one of its constants.
      if (!simple.isEmpty() && !text.contains(simple) && !referenced.contains(owner)) {
        missing.add(owner);
      }
    }
    if (missing.isEmpty()) {
      return text;
    }

    List<String> imports = imports(text);
    String packageName = packageName(text);
    String nest = root == null || root.classStruct == null ? "" : root.classStruct.qualifiedName;
    Map<String, List<Constant>> candidates = new HashMap<>();
    for (String owner : missing) {
      if (isBootstrapOwner(owner)) {
        continue; // present for a lambda/indy bootstrap, never a source-named constant owner
      }
      StructClass cls = DecompilerContext.getStructContext().getClass(owner);
      if (cls == null) {
        continue;
      }
      boolean samePackage = packageName.equals(packageOf(owner));
      boolean imported = imports.contains(simpleName(owner));
      if (!samePackage && !imported && owner.contains("$")) {
        continue; // a nested class's binary name cannot be written in source
      }
      for (StructField field : cls.getFields()) {
        if ((field.getAccessFlags() & (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL))
            != (CodeConstants.ACC_STATIC | CodeConstants.ACC_FINAL)) {
          continue;
        }
        int access = field.getAccessFlags();
        boolean accessible = (access & CodeConstants.ACC_PUBLIC) != 0
          || ((access & CodeConstants.ACC_PRIVATE) == 0 && samePackage)
          || ((access & CodeConstants.ACC_PRIVATE) != 0 && nestOf(owner).equals(nest));
        if (!accessible) {
          continue;
        }
        StructConstantValueAttribute attribute =
          field.getAttribute(StructGeneralAttribute.ATTRIBUTE_CONSTANT_VALUE);
        if (attribute == null) {
          continue;
        }
        PrimitiveConstant value = cls.getPool().getPrimitiveConstant(attribute.getIndex());
        if (value == null || value.value == null) {
          continue;
        }
        VariableType kind = kind(field.getDescriptor());
        if (kind == null) {
          continue;
        }
        String printed = kind == VariableType.BOOLEAN && value.value instanceof Integer flag
          ? Boolean.toString(flag != 0) : String.valueOf(value.value);
        String key = kind + "|" + printed;
        candidate(candidates, key, new Constant(owner, field.getName(), kind));
      }
    }
    if (candidates.isEmpty()) {
      return text;
    }

    List<Site> sites = new ArrayList<>();
    scan(text, candidates, imports, packageName, sites);
    if (sites.isEmpty()) {
      return text;
    }
    StringBuilder builder = new StringBuilder(text);
    for (int i = sites.size() - 1; i >= 0; i--) {
      Site site = sites.get(i);
      builder.replace(site.start(), site.end(), site.replacement());
    }
    return builder.toString();
  }

  private static boolean isBootstrapOwner(String owner) {
    return owner.startsWith("java/lang/invoke/")
      || owner.equals("java/lang/runtime/ObjectMethods")
      || owner.equals("java/lang/runtime/SwitchBootstraps")
      || owner.startsWith("java/lang/constant/");
  }

  private static void candidate(Map<String, List<Constant>> map, String key, Constant constant) {
    map.computeIfAbsent(key, k -> new ArrayList<>()).add(constant);
  }

  private static void collectPool(ClassNode node, Set<String> present, Set<String> referenced) {
    if (node == null) {
      return;
    }
    StructClass cls = node.classStruct;
    if (cls != null) {
      for (PooledConstant constant : cls.getPool().getPool()) {
        if (constant instanceof PrimitiveConstant primitive && primitive.type == CodeConstants.CONSTANT_Class
            && primitive.getString() != null) {
          present.add(primitive.getString());
        } else if (constant instanceof LinkConstant link && link.classname != null) {
          referenced.add(link.classname);
        }
      }
    }
    for (ClassNode nested : node.nested) {
      collectPool(nested, present, referenced);
    }
  }

  private static VariableType kind(String descriptor) {
    return switch (descriptor) {
      // A byte or short constant folded into an int literal changes the expression's type when it
      // is named (Pair.of(5) infers Integer, Pair.of(BYTE_CONST) infers Byte), so those owners are
      // never candidates for a plain integer literal.
      case "I" -> VariableType.INT;
      case "C" -> VariableType.CHAR;
      case "Z" -> VariableType.BOOLEAN;
      case "J" -> VariableType.LONG;
      case "F" -> VariableType.FLOAT;
      case "D" -> VariableType.DOUBLE;
      case "Ljava/lang/String;" -> VariableType.STRING;
      default -> null;
    };
  }

  private static String simpleName(String internal) {
    String name = internal.substring(internal.lastIndexOf('/') + 1);
    int dollar = name.lastIndexOf('$');
    return dollar < 0 ? name : name.substring(dollar + 1);
  }

  /** The top-level class a nest belongs to; private members are shared inside one nest only. */
  private static String nestOf(String internal) {
    int dollar = internal.indexOf('$');
    return dollar < 0 ? internal : internal.substring(0, dollar);
  }

  private static String packageOf(String internal) {
    int slash = internal.lastIndexOf('/');
    return slash < 0 ? "" : internal.substring(0, slash).replace('/', '.');
  }

  private static List<String> imports(String text) {
    List<String> imports = new ArrayList<>();
    for (String line : text.split("\n")) {
      String trimmed = line.trim();
      if (trimmed.startsWith("import ") && trimmed.endsWith(";")) {
        String name = trimmed.substring("import ".length(), trimmed.length() - 1).trim();
        if (name.startsWith("static ")) {
          name = name.substring("static ".length()).trim();
        }
        int dot = name.lastIndexOf('.');
        imports.add(dot < 0 ? name : name.substring(dot + 1));
      }
    }
    return imports;
  }

  private static String packageName(String text) {
    for (String line : text.split("\n")) {
      String trimmed = line.trim();
      if (trimmed.startsWith("package ") && trimmed.endsWith(";")) {
        return trimmed.substring("package ".length(), trimmed.length() - 1).trim();
      }
    }
    return "";
  }

  // ------------------------------------------------------------------ literal scanning

  private static void scan(String text, Map<String, List<Constant>> candidates, List<String> imports,
                           String packageName, List<Site> sites) {
    int i = 0;
    while (i < text.length()) {
      char c = text.charAt(i);
      char next = i + 1 < text.length() ? text.charAt(i + 1) : '\0';
      if (c == '/' && next == '/') {
        i = text.indexOf('\n', i);
        if (i < 0) {
          break;
        }
        continue;
      }
      if (c == '/' && next == '*') {
        int end = text.indexOf("*/", i + 2);
        i = end < 0 ? text.length() : end + 2;
        continue;
      }
      if (c == '"') {
        int end = skipQuoted(text, i, '"');
        if (!text.startsWith("\"\"\"", i) && end - 1 > i) {
          String value = unescape(text.substring(i + 1, end - 1));
          if (value != null && !value.isEmpty()) {
            addSite(sites, i, end, VariableType.STRING + "|" + value, candidates, imports, packageName);
          }
        }
        i = end;
        continue;
      }
      if (c == '\'') {
        int end = skipQuoted(text, i, '\'');
        if (end - 1 > i) {
          Integer value = charValue(text.substring(i + 1, end - 1));
          if (value != null) {
            addSite(sites, i, end, VariableType.CHAR + "|" + value, candidates, imports, packageName);
          }
        }
        i = end;
        continue;
      }
      if (Character.isLetter(c) && (i == 0 || !isIdentifierPart(text.charAt(i - 1)))) {
        int end = i;
        while (end < text.length() && isIdentifierPart(text.charAt(end))) {
          end++;
        }
        String word = text.substring(i, end);
        if (word.equals("true") || word.equals("false")) {
          addSite(sites, i, end, VariableType.BOOLEAN + "|" + word, candidates, imports, packageName);
        }
        i = end;
        continue;
      }
      if (Character.isDigit(c) && (i == 0 || !isIdentifierPart(text.charAt(i - 1)))) {
        i = scanNumber(text, i, sites, candidates, imports, packageName);
        continue;
      }
      i++;
    }
  }

  /** The '-' of a unary minus directly before this literal, or -1 for a binary minus. */
  private static int unaryMinusAt(String text, int start) {
    int i = start - 1;
    while (i >= 0 && Character.isWhitespace(text.charAt(i))) {
      i--;
    }
    if (i < 0 || text.charAt(i) != '-') {
      return -1;
    }
    int before = i - 1;
    while (before >= 0 && Character.isWhitespace(text.charAt(before))) {
      before--;
    }
    if (before < 0) {
      return i;
    }
    char c = text.charAt(before);
    return Character.isLetterOrDigit(c) || c == '_' || c == ')' || c == ']' || c == '"' || c == '\'' ? -1 : i;
  }

  private static int scanNumber(String text, int start, List<Site> sites,
                                Map<String, List<Constant>> candidates, List<String> imports,
                                String packageName) {
    int i = start;
    char c = text.charAt(i);
    boolean hex = c == '0' && i + 1 < text.length()
      && (text.charAt(i + 1) == 'x' || text.charAt(i + 1) == 'X'
          || text.charAt(i + 1) == 'b' || text.charAt(i + 1) == 'B');
    if (hex) {
      i += 2;
      while (i < text.length() && (Character.digit(text.charAt(i), 16) >= 0 || text.charAt(i) == '_')) {
        i++;
      }
    } else {
      boolean dot = false;
      boolean exponent = false;
      while (i < text.length()) {
        char digit = text.charAt(i);
        if (Character.isDigit(digit) || digit == '_') {
          i++;
          continue;
        }
        if (digit == '.' && !dot && !exponent) {
          dot = true;
          i++;
          continue;
        }
        if ((digit == 'e' || digit == 'E') && !exponent) {
          exponent = true;
          i++;
          if (i < text.length() && (text.charAt(i) == '+' || text.charAt(i) == '-')) {
            i++;
          }
          continue;
        }
        break;
      }
    }
    int negativeAt = unaryMinusAt(text, start);
    boolean negative = negativeAt >= 0;
    String digits = text.substring(start, i).replace("_", "");
    char suffix = hex || i >= text.length() ? '\0' : text.charAt(i);
    String kind;
    String value;
    try {
      if (suffix == 'f' || suffix == 'F') {
        i++;
        kind = VariableType.FLOAT.name();
        float parsedFloat = Float.parseFloat(digits);
        value = Float.toString(negative ? -parsedFloat : parsedFloat);
      } else if (suffix == 'd' || suffix == 'D') {
        i++;
        kind = VariableType.DOUBLE.name();
        double parsedDouble = Double.parseDouble(digits);
        value = Double.toString(negative ? -parsedDouble : parsedDouble);
      } else if (suffix == 'l' || suffix == 'L') {
        i++;
        Long parsed = parseLong(digits);
        if (parsed == null) {
          return i;
        }
        kind = VariableType.LONG.name();
        value = Long.toString(negative ? -parsed : parsed);
      } else if (digits.indexOf('.') >= 0 || digits.indexOf('e') >= 0 || digits.indexOf('E') >= 0) {
        kind = VariableType.DOUBLE.name();
        double parsedDouble = Double.parseDouble(digits);
        value = Double.toString(negative ? -parsedDouble : parsedDouble);
      } else {
        Long parsed = parseLong(digits);
        if (parsed == null) {
          return i;
        }
        kind = VariableType.INT.name();
        value = Long.toString(negative ? -parsed : parsed);
      }
    } catch (NumberFormatException e) {
      return i;
    }
    addSite(sites, negative ? negativeAt : start, i, kind + "|" + value, candidates, imports, packageName);
    return i;
  }

  private static void addSite(List<Site> sites, int start, int end, String key,
                              Map<String, List<Constant>> candidates, List<String> imports,
                              String packageName) {
    List<Constant> constants = candidates.get(key);
    if (constants == null || constants.size() != 1 || tooCommon(key)) {
      return;
    }
    Constant constant = constants.get(0);
    String name = simpleName(constant.owner());
    String printed = name + "." + constant.name();
    if (!(imports.contains(name) || packageName.equals(packageOf(constant.owner())))) {
      if (constant.owner().contains("$")) {
        return;
      }
      printed = constant.owner().replace('/', '.') + "." + constant.name();
    }
    sites.add(new Site(start, end, printed));
  }

  /**
   * Small, frequent values have a constant declaration in almost every library; a rewrite at such
   * a site is a coincidence, not evidence, and cannot be checked without compiling.
   */
  private static boolean tooCommon(String key) {
    if (key.startsWith(VariableType.BOOLEAN + "|")) {
      return true;
    }
    if (key.startsWith(VariableType.INT + "|") || key.startsWith(VariableType.LONG + "|")) {
      try {
        long value = Long.parseLong(key.substring(key.indexOf('|') + 1));
        return value >= -3 && value <= 3;
      } catch (NumberFormatException e) {
        return true;
      }
    }
    if (key.startsWith(VariableType.CHAR + "|")) {
      try {
        int value = Integer.parseInt(key.substring(key.indexOf('|') + 1));
        return value < 32 || Character.isLetterOrDigit(value);
      } catch (NumberFormatException e) {
        return true;
      }
    }
    if (key.startsWith(VariableType.STRING + "|")) {
      return key.length() < VariableType.STRING.name().length() + 4;
    }
    return false;
  }

  private static int skipQuoted(String text, int start, char quote) {
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
      if (c == '\n') {
        return i;
      }
      i++;
    }
    return text.length();
  }

  private static String unescape(String body) {
    StringBuilder builder = new StringBuilder(body.length());
    for (int i = 0; i < body.length(); i++) {
      char c = body.charAt(i);
      if (c != '\\') {
        builder.append(c);
        continue;
      }
      if (i + 1 >= body.length()) {
        return null;
      }
      char escaped = body.charAt(++i);
      switch (escaped) {
        case 'n' -> builder.append('\n');
        case 't' -> builder.append('\t');
        case 'r' -> builder.append('\r');
        case 'b' -> builder.append('\b');
        case 'f' -> builder.append('\f');
        case '\'' -> builder.append('\'');
        case '\\' -> builder.append('\\');
        case '"' -> builder.append('"');
        case 'u' -> {
          if (i + 4 >= body.length()) {
            return null;
          }
          builder.append((char) Integer.parseInt(body.substring(i + 1, i + 5), 16));
          i += 4;
        }
        default -> {
          return null;
        }
      }
    }
    return builder.toString();
  }

  private static Integer charValue(String body) {
    String unescaped = unescape(body);
    return unescaped != null && unescaped.length() == 1 ? (int) unescaped.charAt(0) : null;
  }

  private static Long parseLong(String digits) {
    try {
      if (digits.startsWith("0x") || digits.startsWith("0X")) {
        return Long.parseLong(digits.substring(2), 16);
      }
      if (digits.startsWith("0b") || digits.startsWith("0B")) {
        return Long.parseLong(digits.substring(2), 2);
      }
      return Long.parseLong(digits);
    } catch (NumberFormatException e) {
      return null;
    }
  }

  private static boolean isIdentifierPart(char c) {
    return Character.isJavaIdentifierPart(c);
  }
}
