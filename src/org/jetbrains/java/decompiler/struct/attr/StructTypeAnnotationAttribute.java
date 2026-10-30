// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.struct.attr;

import org.jetbrains.java.decompiler.code.BytecodeVersion;
import org.jetbrains.java.decompiler.modules.decompiler.exps.AnnotationExprent;
import org.jetbrains.java.decompiler.modules.decompiler.exps.TypeAnnotation;
import org.jetbrains.java.decompiler.struct.consts.ConstantPool;
import org.jetbrains.java.decompiler.util.DataInputFullStream;

import java.io.DataInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class StructTypeAnnotationAttribute extends StructGeneralAttribute {
  private List<TypeAnnotation> annotations = Collections.emptyList();
  /**
   * One row of a {@code localvar_target} table. A single annotation can cover several locals, so the
   * path and annotation are shared and only the range and slot vary.
   */
  private List<LocalTypeAnnotation> localAnnotations = Collections.emptyList();

  public record LocalTypeAnnotation(int startPc, int length, int index, TypeAnnotation.PathValue[] path, AnnotationExprent annotation) {
  }

  @Override
  public void initContent(DataInputFullStream data, ConstantPool pool, BytecodeVersion version) throws IOException {
    int len = data.readUnsignedShort();
    if (len > 0) {
      annotations = new ArrayList<>(len);
      localAnnotations = new ArrayList<>();
      for (int i = 0; i < len; i++) {
        parse(data, pool);
      }
      if (localAnnotations.isEmpty()) {
        localAnnotations = Collections.emptyList();
      }
    }
    else {
      annotations = Collections.emptyList();
      localAnnotations = Collections.emptyList();
    }
  }

  private void parse(DataInputStream data, ConstantPool pool) throws IOException {
    int targetType = data.readUnsignedByte();
    int target = targetType << 24;
    int[] localRows = null;

    switch (targetType) {
      case TypeAnnotation.CLASS_TYPE_PARAMETER:
      case TypeAnnotation.METHOD_TYPE_PARAMETER:
      case TypeAnnotation.METHOD_PARAMETER:
        target |= data.readUnsignedByte();
        break;

      case TypeAnnotation.SUPER_TYPE_REFERENCE:
      case TypeAnnotation.CLASS_TYPE_PARAMETER_BOUND:
      case TypeAnnotation.METHOD_TYPE_PARAMETER_BOUND:
      case TypeAnnotation.THROWS_REFERENCE:
      case TypeAnnotation.CATCH_CLAUSE:
      case TypeAnnotation.EXPR_INSTANCEOF:
      case TypeAnnotation.EXPR_NEW:
      case TypeAnnotation.EXPR_CONSTRUCTOR_REF:
      case TypeAnnotation.EXPR_METHOD_REF:
        target |= data.readUnsignedShort();
        break;

      case TypeAnnotation.TYPE_ARG_CAST:
      case TypeAnnotation.TYPE_ARG_CONSTRUCTOR_CALL:
      case TypeAnnotation.TYPE_ARG_METHOD_CALL:
      case TypeAnnotation.TYPE_ARG_CONSTRUCTOR_REF:
      case TypeAnnotation.TYPE_ARG_METHOD_REF:
        data.skipBytes(3);
        break;

      case TypeAnnotation.LOCAL_VARIABLE:
      case TypeAnnotation.RESOURCE_VARIABLE:
        int count = data.readUnsignedShort();
        localRows = new int[count * 3];
        for (int i = 0; i < count; i++) {
          localRows[i * 3] = data.readUnsignedShort();
          localRows[i * 3 + 1] = data.readUnsignedShort();
          localRows[i * 3 + 2] = data.readUnsignedShort();
        }
        break;

      case TypeAnnotation.FIELD:
      case TypeAnnotation.METHOD_RETURN_TYPE:
      case TypeAnnotation.METHOD_RECEIVER:
        break;

      default:
        throw new RuntimeException("unknown target type: " + targetType);
    }

    int pathLength = data.readUnsignedByte();
    TypeAnnotation.PathValue[] path = new TypeAnnotation.PathValue[pathLength];
    for (int i = 0; i < pathLength; i++) {
      path[i] = new TypeAnnotation.PathValue(TypeAnnotation.PathKind.VALUES[data.readByte()], data.readByte());
    }

    AnnotationExprent annotation = StructAnnotationAttribute.parseAnnotation(data, pool);

    annotations.add(new TypeAnnotation(target, path, annotation));

    if (localRows != null) {
      for (int i = 0; i < localRows.length; i += 3) {
        localAnnotations.add(new LocalTypeAnnotation(localRows[i], localRows[i + 1], localRows[i + 2], path, annotation));
      }
    }
  }

  /**
   * Fold the annotations of a Code attribute into a method-level table. javac writes
   * local-variable targets (0x40, 0x41) on the Code attribute and every other target on the
   * method, so one source annotation list arrives as two attributes that must both survive:
   * the map holds one value per key, and overwriting either table loses the other one's
   * positions.
   */
  public void merge(StructTypeAnnotationAttribute other) {
    if (other.annotations.isEmpty() && other.localAnnotations.isEmpty()) {
      return;
    }

    List<TypeAnnotation> combined = new ArrayList<>(annotations.size() + other.annotations.size());
    combined.addAll(annotations);
    combined.addAll(other.annotations);
    annotations = combined;

    List<LocalTypeAnnotation> locals = new ArrayList<>(localAnnotations.size() + other.localAnnotations.size());
    locals.addAll(localAnnotations);
    locals.addAll(other.localAnnotations);
    localAnnotations = locals;
  }

  public List<TypeAnnotation> getAnnotations() {
    return annotations;
  }

  /** The annotations written against local variables, one entry per (range, slot) row. */
  public List<LocalTypeAnnotation> getLocalAnnotations() {
    return localAnnotations;
  }

  public void setAnnotations(List<TypeAnnotation> annotations) {
    this.annotations = annotations;
  }
}