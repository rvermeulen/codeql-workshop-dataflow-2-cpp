/**
 * @kind path-problem
 */

import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import semmle.code.cpp.controlflow.Guards
import DataFlow::PathGraph

class MyConfig extends DataFlow::Configuration {
  MyConfig() { this = "MyConfig" }

  override predicate isSource(DataFlow::Node n) {
    exists(FunctionCall call | call.getTarget().hasName("source1") |
      // Here we use `asIndirectExpr` instead of `asExpr` because we are interested in tracking the value
      // pointed to by the returned pointer and not the value of the pointer itself (address of the value).
      n.asIndirectExpr() = call
    )
    or
    exists(FunctionCall call | call.getTarget().hasName("source2") |
      call.getArgument(0) = n.asDefiningArgument()
    )
  }

  override predicate isSink(DataFlow::Node n) {
    exists(FunctionCall call | call.getTarget().hasName("sink") |
      // Here we use `asIndirectArgument(1)` instead of `asExpr` because we are interested in the value after one dereference.
      call.getAnArgument() = n.asIndirectArgument(1)
    )
  }

  override predicate isBarrier(DataFlow::Node n) {
    // The new data flow framework uses use-use flows so compared to the old framework we have the edge
    // [parameter ptr] --> [argument ptr in call to sanitize] --> [argument ptr in call to sink]
    // Marking the argument to sanitize as a barrier is sufficient to stop the flow to sink.
    exists(FunctionCall call | call.getTarget().hasName("sanitize") |
      // Here we use `asIndirectArgument` instead of `asExpr` because we are interested in the tracked value instead of the value of the pointer.
      call.getAnArgument() = n.asIndirectArgument()
    )
    or
    exists(GuardCondition gc, FunctionCall call, Variable v, VariableAccess safeAccess |
      call.getTarget().hasName("valid") and gc = call
    |
      call.getAnArgument() = v.getAnAccess() and
      safeAccess = v.getAnAccess() and
      // Here we use `asIndirectExpr` instead of `asExpr` because we are interested in the tracked value instead of the value of the pointer.
      safeAccess = n.asIndirectExpr() and
      gc.controls(safeAccess.getBasicBlock(), true)
    )
  }

  override predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2) {
    exists(FunctionCall call | call.getTarget().hasName("append") |
    // Here we use `asIndirectArgument` instead of `asExpr` because we are interested in the tracked value instead of the value of the pointer.
      call.getArgument(0) = node1.asIndirectArgument() and
      // Here we use `asIndirectExpr` instead of `asExpr` because we are interested in the tracked value instead of the value of the pointer.
      call = node2.asIndirectExpr()
    )
  }
}

from MyConfig config, DataFlow::PathNode source, DataFlow::PathNode sink
where config.hasFlowPath(source, sink)
select sink, source, sink, "Insecure usage of sink"
