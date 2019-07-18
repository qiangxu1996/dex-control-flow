package edu.purdue.ddf;

import org.jf.dexlib2.builder.*;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.DominatorTree;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.MHGPostDominatorsFinder;

import java.util.*;

/**
 * Represents the control flow graph of a given method.
 *
 * <p>To obtain the control flow graph, do the following:</p>
 *
 * <pre>MutableMethodImplementation m = ...
 * ControlFlow cf = new ControlFlow(m);
 * Block[] blocks = cf.basicBlocks();
 * </pre>
 *
 * <p><code>blocks</code> is an array of basic blocks in
 * that method body.</p>
 *
 * @see Block
 * @author Qiang Xu
 */
public class ControlFlow {
	private Block[] basicBlocks;

	/**
	 * Basic block.
	 * It is a sequence of contiguous instructions that do not contain
	 * jump/branch instructions except the last one.
	 */
	public static class Block {
		/**
		 * A field that can be freely used for storing extra data.
		 * A client program of this control-flow analyzer can append
		 * an additional attribute to a {@link Block} object.
		 */
		public Object clientData = null;

		int position;

		int length;

		Block[] entrances;

		Block[] exits;

		Block(int pos) {
			position = pos;
		}
	}

	static class BlockBuilder {
		/**
		 * A Mark indicates the position of a branch instruction or a branch target.
		 * Each basic block may have 1 or 2 marks.
		 * The first mark is a {@link #leader},
		 * and we need to put a link connecting the next block if this block is not {@link #uncond}.
		 */
		static class Mark implements Comparable<Mark> {
			int position;

			boolean leader;

			boolean uncond;

			/**
			 * Not empty only if {@link #leader}.
			 */
			List<Mark> entrances = new ArrayList<>();

			List<Mark> exits = new ArrayList<>();

			/**
			 * Used in the second iteration.
			 */
			Block block;

			Mark(int pos) {
				position = pos;
			}

			@Override
			public int compareTo(Mark o) {
				return position - o.position;
			}
		}

		static class MarksMgr {
			Map<Integer, Mark> marks;

			MarksMgr(Map<Integer, Mark> marks) {
				this.marks = marks;
			}

			Mark addLeader(int pos) {
				var m = marks.computeIfAbsent(pos, p -> {
					var mm = new Mark(p);
					mm.uncond = false;
					return mm;
				});
				m.leader = true;
				return m;
			}

			Mark addCtrl(int pos, boolean uncond) {
				var m = marks.computeIfAbsent(pos, p -> {
					var mm = new Mark(p);
					mm.leader = false;
					return mm;
				});
				m.uncond = uncond;
				return m;
			}

			Mark addCtrl(int pos, boolean uncond, Mark exit) {
				var m = addCtrl(pos, uncond);

				m.exits.add(exit);
				exit.entrances.add(m);

				return m;
			}
			Mark addCtrl(int pos, boolean uncond, List<Mark> exits) {
				var m = addCtrl(pos, uncond);

				m.exits.addAll(exits);
				for (var e : exits)
					e.entrances.add(m);

				return m;
			}
		}

		Block[] make(MutableMethodImplementation methodImpl) {
			if (methodImpl == null)
				return new Block[0];
			var insns = methodImpl.getInstructions();
			return make(insns, 0, insns.size(), methodImpl.getTryBlocks());
		}

		/**
		 * @param end exclusive
		 */
		Block[] make(List<BuilderInstruction> insns, int begin, int end, List<BuilderTryBlock> tb) {
			var marks = makeMarks(insns, begin, end, tb);
			return makeBlocks(marks, begin, end);
		}

		private MethodLocation targetLocation(BuilderInstruction insn) {
			return ((BuilderOffsetInstruction) insn).getTarget().getLocation();
		}

		/**
		 * @param end exclusive
		 */
		private Map<Integer, Mark> makeMarks(
				List<BuilderInstruction> insns, int begin, int end, List<BuilderTryBlock> tb) {
			var marks = new HashMap<Integer, Mark>();
			var marksMgr = new MarksMgr(marks);

			/* Ref: Compilers: Principles, Techniques, & Tools (Second Edition) */
			/* 1. The first instruction is a leader. */
			if (end - begin > 0)
				marksMgr.addLeader(begin);

			for (int i = begin; i < end; i++) {
				var insn = insns.get(i);
				boolean ctrl = true;

				/* 2. Any instruction that is the target of a conditional or unconditional jump is a leader. */
				/* Link type 1: There is a conditional or unconditional jump from the end of B to the beginning of C */
				switch (insn.getOpcode()) {
					case RETURN_VOID:
					case RETURN:
					case RETURN_WIDE:
					case RETURN_OBJECT:
					case THROW:
						marksMgr.addCtrl(i, true);
						break;
					case GOTO:
					case GOTO_16:
					case GOTO_32:
						var t = marksMgr.addLeader(targetLocation(insn).getIndex());
						marksMgr.addCtrl(i, true, t);
						break;
					case PACKED_SWITCH:
					case SPARSE_SWITCH:
						var payload = (BuilderSwitchPayload) targetLocation(insn).getInstruction();
						assert payload != null;
						var switchEls = payload.getSwitchElements();
						var exits = new ArrayList<Mark>();
						for (var e : switchEls)
							exits.add(marksMgr.addLeader(e.getTarget().getLocation().getIndex()));
						marksMgr.addCtrl(i, false, exits);
						break;
					case IF_EQ:
					case IF_NE:
					case IF_LT:
					case IF_GE:
					case IF_GT:
					case IF_LE:
					case IF_EQZ:
					case IF_NEZ:
					case IF_LTZ:
					case IF_GEZ:
					case IF_GTZ:
					case IF_LEZ:
						var to = marksMgr.addLeader(targetLocation(insn).getIndex());
						marksMgr.addCtrl(i, false, to);
						break;
					default:
						ctrl = false;
				}

				/* 3. Any instruction that immediately follows a conditional or unconditional jump is a leader. */
				if (ctrl && i + 1 < end)
					marksMgr.addLeader(i + 1);
			}

			/* Treat THROW as unconditional jump and the first insn in exception handler as leader. */
			/* We don't add links between THROW and exception handler, as these links may be inter-procedural. */
			for (var t : tb)
				marksMgr.addLeader(t.exceptionHandler.getHandler().getLocation().getIndex());

			return marks;
		}

		private void extractLinks(Mark mark, List<Block> entrances, List<Block> exits) {
			for (var e : mark.entrances)
				entrances.add(e.block);
			for (var e : mark.exits)
				exits.add(e.block);
		}

		private Block[] makeBlocks(Map<Integer, Mark> markMap, int begin, int end) {
			if (markMap.size() == 0)
				return new Block[0];

			var marks = markMap.values().toArray(new Mark[0]);
			Arrays.sort(marks);

			var marksWithSentinel = Arrays.copyOf(marks, marks.length + 1);
			var sentinel = new Mark(end);
			sentinel.leader = true;
			marksWithSentinel[marks.length] = sentinel;

			/* Attach block to each mark */
			Mark currMark = marksWithSentinel[0];
			Block currBlock = new Block(currMark.position);
			currMark.block = currBlock;
			for (int i = 1; i < marksWithSentinel.length; i++) {
				currMark = marksWithSentinel[i];
				if (currMark.leader) {
					currBlock.length = currMark.position - currBlock.position;
					currBlock = new Block(currMark.position);
				}
				currMark.block = currBlock;
			}

			/* Link type 2: C immediately follows B, and B does not end in an unconditional jump. */
			currMark = marks[0];
			Mark prevMark;
			for (int i = 1; i < marks.length; i++) {
				prevMark = currMark;
				currMark = marks[i];
				if (currMark.leader && !prevMark.uncond) {
					prevMark.exits.add(currMark);
					currMark.entrances.add(prevMark);
				}
			}

			/* Put the links in marks to blocks */
			currMark = marksWithSentinel[0];
			currBlock = currMark.block;
			var currEntrances = new ArrayList<Block>();
			var currExits = new ArrayList<Block>();
			extractLinks(currMark, currEntrances, currExits);
			for (int i = 1; i < marksWithSentinel.length; i++) {
				currMark = marksWithSentinel[i];
				if (currMark.leader) {
					currBlock.entrances = currEntrances.toArray(new Block[0]);
					currBlock.exits = currExits.toArray(new Block[0]);

					currEntrances.clear();
					currExits.clear();
					currBlock = currMark.block;
				}
				extractLinks(currMark, currEntrances, currExits);
			}

			/* Extract the blocks */
			var blocks = new ArrayList<Block>();
			for (var m : marks)
				if (m.leader)
					blocks.add(m.block);

			return blocks.toArray(new Block[0]);
		}
	}

	static class CFG implements DirectedGraph<Block> {
		final Block[] blocks;

		List<Block> heads = new ArrayList<>();

		List<Block> tails = new ArrayList<>();

		CFG(Block[] blocks) {
			this.blocks = blocks;
			for (var b : blocks) {
				if (b.entrances.length == 0)
					heads.add(b);
				if (b.exits.length == 0)
					tails.add(b);
			}
		}

		@Override
		public List<Block> getHeads() {
			return heads;
		}

		@Override
		public List<Block> getTails() {
			return tails;
		}

		@Override
		public List<Block> getPredsOf(Block s) {
			return Arrays.asList(s.entrances);
		}

		@Override
		public List<Block> getSuccsOf(Block s) {
			return Arrays.asList(s.exits);
		}

		@Override
		public int size() {
			return blocks.length;
		}

		@Override
		public Iterator<Block> iterator() {
			return new Iterator<>() {
				int i = 0;

				@Override
				public boolean hasNext() {
					return i < blocks.length;
				}

				@Override
				public Block next() {
					if (!hasNext())
						throw new NoSuchElementException();
					return blocks[i++];
				}
			};
		}
	}

	/**
	 * Constructs a control-flow analyzer for the given method.
	 * {@link MutableMethodImplementation} is required because its instructions are of type {@link BuilderInstruction}.
	 */
	public ControlFlow(MutableMethodImplementation methodImpl) {
		basicBlocks = new BlockBuilder().make(methodImpl);
	}

	/**
	 * Returns all the basic blocks in the method body.
	 *
	 * @return an array of basic blocks, the array has length 0 if
	 * the method doesn't have code.
	 */
	public Block[] basicBlocks() {
		return basicBlocks;
	}

	public DominatorTree<Block> dominatorTree() {
		return new DominatorTree<>(new MHGDominatorsFinder<>(new CFG(basicBlocks)));
	}

	public DominatorTree<Block> postDominatorTree() {
		return new DominatorTree<>(new MHGPostDominatorsFinder<>(new CFG(basicBlocks)));
	}
}
