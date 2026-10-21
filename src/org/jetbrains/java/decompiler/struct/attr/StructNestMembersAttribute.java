package org.jetbrains.java.decompiler.struct.attr;

import org.jetbrains.java.decompiler.code.BytecodeVersion;
import org.jetbrains.java.decompiler.struct.consts.ConstantPool;
import org.jetbrains.java.decompiler.struct.consts.PooledConstant;
import org.jetbrains.java.decompiler.struct.consts.PrimitiveConstant;
import org.jetbrains.java.decompiler.util.DataInputFullStream;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

/*
  NestMembers_attribute {
    u2 attribute_name_index;
    u4 attribute_length;
    u2 number_of_classes;
    u2 classes[number_of_classes];
  }
 */
public class StructNestMembersAttribute extends StructGeneralAttribute {
  private int[] classes;

  @Override
  public void initContent(DataInputFullStream data, ConstantPool pool, BytecodeVersion version) throws IOException {
    int count = data.readUnsignedShort();
    classes = new int[count];
    for (int i = 0; i < count; i++) {
      classes[i] = data.readUnsignedShort();
    }
  }

  public List<String> getClasses(ConstantPool pool) {
    List<String> names = new ArrayList<>();
    for (int index : classes) {
      PooledConstant constant = pool.getConstant(index);
      if (constant instanceof PrimitiveConstant primitive && primitive.getString() != null) {
        names.add(primitive.getString());
      }
    }
    return names;
  }
}
