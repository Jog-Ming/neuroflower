// Copyright 2000-2025 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package org.jetbrains.java.decompiler.struct.attr;

import org.jetbrains.java.decompiler.code.BytecodeVersion;
import org.jetbrains.java.decompiler.struct.consts.ConstantPool;
import org.jetbrains.java.decompiler.util.DataInputFullStream;

import java.io.IOException;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

/**
 * u2 number_of_entries;
 * { u1 frame_type; ... } stack_map_frame[number_of_entries];
 *
 * <p>Only each frame's local-variable state is kept. A frame records which slots javac still held
 * at that branch target, so a slot the table names nowhere but the frame keeps alive is a scope
 * the source wrote and the tree's statements cannot show by themselves.
 *
 * <p>Frames are stored as their delta-encoded shapes; the implicit first frame (the method's
 * parameters) is supplied when a frame is read, so the same attribute serves every method.
 */
public class StructStackMapTableAttribute extends StructGeneralAttribute {
  /** One frame's effect on the local array: a keep, a chop of its last entries, or new entries. */
  public static final class Frame {
    public final int offset;
    /** Slots removed from the end (a chop frame), or 0. */
    public final int chop;
    /** Verification tags appended (an append frame), or null. */
    public final int[] append;
    /** The whole local array (a full frame), or null. */
    public final int[] full;

    Frame(int offset, int chop, int[] append, int[] full) {
      this.offset = offset;
      this.chop = chop;
      this.append = append;
      this.full = full;
    }
  }

  private List<Frame> frames = List.of();

  @Override
  public void initContent(DataInputFullStream data, ConstantPool pool, BytecodeVersion version) throws IOException {
    int count = data.readUnsignedShort();
    List<Frame> parsed = new ArrayList<>(count);
    int offset = -1;
    for (int i = 0; i < count; i++) {
      int type = data.readUnsignedByte();
      if (type <= 63) {
        offset += type + 1;
        parsed.add(new Frame(offset, 0, null, null));
      }
      else if (type <= 127) {
        offset += type - 64 + 1;
        readVti(data); // one stack item, not a local
        parsed.add(new Frame(offset, 0, null, null));
      }
      else if (type <= 246) {
        // Reserved frame types hold no meaning; the table stops giving evidence here.
        return;
      }
      else if (type == 247) {
        offset += data.readUnsignedShort() + 1;
        readVti(data);
        parsed.add(new Frame(offset, 0, null, null));
      }
      else if (type <= 250) {
        offset += data.readUnsignedShort() + 1;
        parsed.add(new Frame(offset, 251 - type, null, null));
      }
      else if (type == 251) {
        offset += data.readUnsignedShort() + 1;
        parsed.add(new Frame(offset, 0, null, null));
      }
      else if (type <= 254) {
        offset += data.readUnsignedShort() + 1;
        int[] tags = new int[type - 251];
        for (int j = 0; j < tags.length; j++) {
          tags[j] = readVti(data);
        }
        parsed.add(new Frame(offset, 0, tags, null));
      }
      else {
        offset += data.readUnsignedShort() + 1;
        int[] tags = new int[data.readUnsignedShort()];
        for (int j = 0; j < tags.length; j++) {
          tags[j] = readVti(data);
        }
        int stack = data.readUnsignedShort();
        for (int j = 0; j < stack; j++) {
          readVti(data);
        }
        parsed.add(new Frame(offset, 0, null, tags));
      }
    }
    frames = parsed;
  }

  private static int readVti(DataInputFullStream data) throws IOException {
    int tag = data.readUnsignedByte();
    if (tag == 7 || tag == 8) { // an object or uninitialized type carries a u2 operand
      data.readUnsignedShort();
    }
    return tag;
  }

  /** The offsets of every recorded frame, in table order. */
  public List<Integer> offsets() {
    List<Integer> out = new ArrayList<>(frames.size());
    for (Frame frame : frames) {
      out.add(frame.offset);
    }
    return out;
  }

  /**
   * The slots javac held in a local at this frame offset, or null when the table has no frame
   * there. {@code initialSlots} is the implicit first frame's length: the method's parameters.
   */
  public BitSet liveLocals(int offset, int initialSlots) {
    if (frames.isEmpty() || offset < 0) {
      return null;
    }
    List<Integer> locals = new ArrayList<>();
    for (int i = 0; i < Math.max(0, initialSlots); i++) {
      locals.add(0);
    }
    for (Frame frame : frames) {
      if (frame.full != null) {
        locals.clear();
        for (int tag : frame.full) {
          locals.add(tag);
        }
      }
      else if (frame.append != null) {
        for (int tag : frame.append) {
          locals.add(tag);
        }
      }
      else {
        for (int k = 0; k < frame.chop && !locals.isEmpty(); k++) {
          locals.remove(locals.size() - 1);
        }
      }
      if (frame.offset == offset) {
        BitSet live = new BitSet();
        for (int slot = 0; slot < locals.size(); slot++) {
          if (locals.get(slot) != 0) { // Top marks a dead slot (and a long's or double's second half)
            live.set(slot);
          }
        }
        return live;
      }
      if (frame.offset > offset) {
        return null;
      }
    }
    return null;
  }
}
