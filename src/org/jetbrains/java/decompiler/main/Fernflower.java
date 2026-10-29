// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.main;

import java.io.IOException;

import org.jetbrains.java.decompiler.api.plugin.LanguageSpec;
import org.jetbrains.java.decompiler.api.plugin.Plugin;
import org.jetbrains.java.decompiler.main.ClassesProcessor.ClassNode;
import org.jetbrains.java.decompiler.main.decompiler.OptionParser;
import org.jetbrains.java.decompiler.main.extern.*;
import org.jetbrains.java.decompiler.main.plugins.JarPluginLoader;
import org.jetbrains.java.decompiler.api.plugin.PluginSource;
import org.jetbrains.java.decompiler.main.plugins.PluginSources;
import org.jetbrains.java.decompiler.modules.decompiler.RoundTrip;
import org.jetbrains.java.decompiler.modules.renamer.ConverterHelper;
import org.jetbrains.java.decompiler.modules.renamer.IdentifierConverter;
import org.jetbrains.java.decompiler.modules.renamer.PoolInterceptor;
import org.jetbrains.java.decompiler.struct.IDecompiledData;
import org.jetbrains.java.decompiler.main.plugins.PluginContext;
import org.jetbrains.java.decompiler.struct.StructClass;
import org.jetbrains.java.decompiler.struct.StructContext;
import org.jetbrains.java.decompiler.struct.attr.StructGeneralAttribute;
import org.jetbrains.java.decompiler.struct.attr.StructSourceFileAttribute;
import org.jetbrains.java.decompiler.util.ClasspathScanner;
import org.jetbrains.java.decompiler.util.JrtFinder;
import org.jetbrains.java.decompiler.util.TextBuffer;
import org.jetbrains.java.decompiler.util.token.TextTokenDumpVisitor;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;

public class Fernflower implements IDecompiledData {
  private final StructContext structContext;
  private final ClassesProcessor classProcessor;
  private final IIdentifierRenamer helper;
  private final IdentifierConverter converter;

  public Fernflower(IResultSaver saver, Map<String, Object> customProperties, IFernflowerLogger logger) {
    this(null, saver, customProperties, logger);
  }

  @Deprecated
  public Fernflower(IBytecodeProvider provider, IResultSaver saver, Map<String, Object> customProperties, IFernflowerLogger logger) {
    Map<String, Object> properties = new HashMap<>(IFernflowerPreferences.DEFAULTS);
    if (customProperties != null) {
      for (Map.Entry<String, Object> entry : customProperties.entrySet()) {
        if (entry.getKey().length() == 3) {
          // Short name, reparse to long name
          OptionParser.parseShort("-" + entry.getKey() + "=" + entry.getValue(), properties);
        } else {
          properties.put(entry.getKey(), entry.getValue());
        }
      }
    }

    String level = (String)properties.get(IFernflowerPreferences.LOG_LEVEL);
    if (level != null) {
      try {
        logger.setSeverity(IFernflowerLogger.Severity.valueOf(level.toUpperCase(Locale.ENGLISH)));
      }
      catch (IllegalArgumentException ignore) { }
    }

    structContext = new StructContext(provider, saver, this);
    classProcessor = new ClassesProcessor(structContext);

    PoolInterceptor interceptor = null;
    if ("1".equals(properties.get(IFernflowerPreferences.RENAME_ENTITIES))) {
      helper = loadHelper((String)properties.get(IFernflowerPreferences.USER_RENAMER_CLASS), logger);
      interceptor = new PoolInterceptor();
      converter = new IdentifierConverter(structContext, helper, interceptor);
    }
    else {
      helper = null;
      converter = null;
    }

    DecompilerContext context = new DecompilerContext(properties, logger, structContext, classProcessor, interceptor);
    DecompilerContext.setCurrentContext(context);

    PluginContext plugins = structContext.getPluginContext();
    int pluginCount = plugins.findPlugins();

    logger.writeMessage("Loaded " + pluginCount + " plugins", IFernflowerLogger.Severity.INFO);

    plugins.initialize();

    IVariableNamingFactory renamer = plugins.getVariableRenamer();
    if (renamer == null) {
      renamer = new IdentityRenamerFactory();
    }

    context.renamerFactory = renamer;

    String vendor = System.getProperty("java.vendor", "missing vendor");
    String javaVersion = System.getProperty("java.version", "missing java version");
    String jvmVersion = System.getProperty("java.vm.version", "missing jvm version");
    logger.writeMessage(String.format("JVM info: %s - %s - %s", vendor, javaVersion, jvmVersion), IFernflowerLogger.Severity.INFO);

    if (DecompilerContext.getOption(IFernflowerPreferences.INCLUDE_ENTIRE_CLASSPATH)) {
      ClasspathScanner.addAllClasspath(structContext);
    } else if (!DecompilerContext.getProperty(IFernflowerPreferences.INCLUDE_JAVA_RUNTIME).toString().isEmpty()) {
      final String javaRuntime = DecompilerContext.getProperty(IFernflowerPreferences.INCLUDE_JAVA_RUNTIME).toString();
      if (javaRuntime.equalsIgnoreCase(JrtFinder.CURRENT) || javaRuntime.equalsIgnoreCase("1")) {
        JrtFinder.addRuntime(structContext);
      } else if (!javaRuntime.equalsIgnoreCase("0")) {
        JrtFinder.addRuntime(structContext, new File(javaRuntime));
      }
    }
  }

  private static IIdentifierRenamer loadHelper(String className, IFernflowerLogger logger) {
    if (className != null) {
      try {
        Class<?> renamerClass = Fernflower.class.getClassLoader().loadClass(className);
        return (IIdentifierRenamer) renamerClass.getDeclaredConstructor().newInstance();
      }
      catch (Exception e) {
        logger.writeMessage("Cannot load renamer '" + className + "'", IFernflowerLogger.Severity.WARN, e);
      }
    }

    return new ConverterHelper();
  }

  public void addSource(IContextSource source) {
    structContext.addSpace(source, true);
  }

  public void addSource(File source) {
    structContext.addSpace(source, true);
  }

  public void addLibrary(IContextSource library) {
    structContext.addSpace(library, false);
  }

  public void addLibrary(File library) {
    structContext.addSpace(library, false);
  }

  public void decompileContext() {
    for (Plugin plugin : this.structContext.getPluginContext().getPlugins()) {
      plugin.beforeDecompile();
    }

    if (converter != null) {
      converter.rename();
    }

    classProcessor.loadClasses(helper);

    structContext.saveContext();
  }

  public void addWhitelist(String prefix) {
    classProcessor.addWhitelist(prefix);
  }

  public void clearContext() {
    structContext.clear();
    DecompilerContext.setCurrentContext(null);
  }

  @Override
  public String getClassEntryName(StructClass cl, String entryName) {
    LanguageSpec spec = PluginContext.getCurrentContext().getLanguageSpec(cl);
    String extension = spec == null ? "java" : spec.extension;

    ClassNode node = classProcessor.getMapRootClasses().get(cl.qualifiedName);
    if (node == null || node.type != ClassNode.Type.ROOT) {
      return null;
    }
    else if (converter != null) {
      String simpleClassName = cl.qualifiedName.substring(cl.qualifiedName.lastIndexOf('/') + 1);
      return entryName.substring(0, entryName.lastIndexOf('/') + 1) + simpleClassName + "." + extension;
    }
    else {
      final int clazzIdx = entryName.lastIndexOf(".class");
      String name = clazzIdx == -1 ? entryName + "." + extension
        : entryName.substring(0, clazzIdx) + "." + extension;
      return "java".equals(extension) ? sourceFileName(cl, entryName, name) : name;
    }
  }

  /**
   * javac records the compiled source file's name in every class it produced. A class can live
   * in a file named after another class — a package-private type beside its public host — and
   * the original name is the only way its bytes carry the same SourceFile attribute. Two such
   * classes cannot share it, so a class whose source file is already a root class's own name
   * goes into a directory of its own.
   */
  private String sourceFileName(StructClass cl, String entryName, String fallback) {
    StructSourceFileAttribute source = cl.getAttribute(StructGeneralAttribute.ATTRIBUTE_SOURCE_FILE);
    if (source == null) {
      return fallback;
    }
    String fileName = source.getSourceFile(cl.getPool());
    String simple = cl.qualifiedName.substring(cl.qualifiedName.lastIndexOf('/') + 1);
    if (fileName == null || !fileName.endsWith(".java") || fileName.equals(simple + ".java")) {
      return fallback;
    }
    int slash = entryName.lastIndexOf('/');
    String directory = slash < 0 ? "" : entryName.substring(0, slash + 1);
    String owner = cl.qualifiedName.substring(0, cl.qualifiedName.lastIndexOf('/') + 1)
      + fileName.substring(0, fileName.length() - ".java".length());
    return classProcessor.getMapRootClasses().containsKey(owner)
      ? directory + simple + "/" + fileName : directory + fileName;
  }

  /** Restores named constants when the pool proves the original wrote one; never compiles. */
  private String named(String text, StructClass cl) {
    if (!RoundTrip.selector("rt-constant-names")) {
      return text;
    }
    try {
      ClassesProcessor.ClassNode root = classProcessor.getMapRootClasses().get(cl.qualifiedName);
      return ConstantNames.restore(text, root);
    } catch (RuntimeException e) {
      return text;
    }
  }

  @Override
  public void processClass(final StructClass cl) throws IOException {
      classProcessor.processClass(cl); // unhandled exceptions handled later on
  }

  @Override
  public String getClassContent(StructClass cl) {
    TextBuffer buffer = new TextBuffer(ClassesProcessor.AVERAGE_CLASS_SIZE);
    try {
      buffer.append(DecompilerContext.getProperty(IFernflowerPreferences.BANNER).toString());
      classProcessor.writeClass(cl, buffer);

      if (RoundTrip.selector("linealign")) {
        try {
          String aligned = LineAlign.align(buffer,
            classProcessor.getMapRootClasses().get(cl.qualifiedName));
          if (aligned != null) {
            // The site-aware pass already ran inside LineAlign on the unaligned text; the old
            // whole-file pass must not run a second time over the aligned text.
            return RoundTrip.selector("rt-constant-sites")
              ? aligned : named(aligned, cl);
          }
        } catch (RuntimeException e) {
          // A class must not be lost because its line table could not be aligned.
        }
      }

      if (DecompilerContext.getOption(IFernflowerPreferences.DUMP_TEXT_TOKENS)) {
        buffer.visitTokens(TextTokenVisitor.createVisitor(next -> new TextTokenDumpVisitor(next, buffer)));
      } else {
        buffer.visitTokens(TextTokenVisitor.createVisitor());
      }

      String res = buffer.convertToStringAndAllowDataDiscard();
      if (res == null) {
        return "$ VF: Unable to decompile class " + cl.qualifiedName;
      }

      return named(res, cl);
    }
    catch (Throwable t) {
      DecompilerContext.getLogger().writeMessage("Class " + cl.qualifiedName + " couldn't be fully decompiled.", t);
      if (DecompilerContext.getOption(IFernflowerPreferences.DUMP_EXCEPTION_ON_ERROR)) {
        List<String> lines = new ArrayList<>();
        lines.add("/*");
        lines.add("$VF: Unable to decompile class");
        lines.addAll(ClassWriter.getErrorComment());
        ClassWriter.collectErrorLines(t, lines);
        lines.add("*/");
        return String.join(DecompilerContext.getNewLineSeparator(), lines);
      } else {
        return null;
      }
    }
  }

  static {
    Init.init();
  }
}