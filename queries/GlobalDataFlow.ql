/**
 * @kind path-problem
 */

import cpp
import semmle.code.cpp.dataflow.DataFlow
import semmle.code.cpp.controlflow.Guards
import DataFlow::PathGraph

class MyConfig extends DataFlow::Configuration {
  MyConfig() { this = "MyConfig" }

  override predicate isSource(DataFlow::Node n) {
    exists(FunctionCall call | call.getTarget().hasName("source1") | n.asExpr() = call)
    or
    exists(FunctionCall call | call.getTarget().hasName("source2") |
      call.getArgument(0) = n.asDefiningArgument()
    )
  }

  override predicate isSink(DataFlow::Node n) {
    exists(FunctionCall call | call.getTarget().hasName("sink") | call.getAnArgument() = n.asExpr())
  }

  override predicate isBarrier(DataFlow::Node n) {
    // This data flow configuration uses def-use flow so there will be the following edges in our example.
    // - [parameter ptr] --> [argument ptr in call to sanitize]
    // - [parameter ptr] --> [argument ptr in call to sink]
    // To remove this second edge we resort to control flow and mark any access to the variable passed to
    // sanitize as a barrier.
    exists(FunctionCall call, Variable v, VariableAccess safeAccess |
      call.getTarget().hasName("sanitize")
    |
      call.getAnArgument() = v.getAnAccess() and
      safeAccess = v.getAnAccess() and
      call.getASuccessor+() = safeAccess and
      safeAccess = n.asExpr()
    )
    or
    exists(GuardCondition gc, FunctionCall call, Variable v, VariableAccess safeAccess |
      call.getTarget().hasName("valid") and gc = call
    |
      call.getAnArgument() = v.getAnAccess() and
      safeAccess = v.getAnAccess() and
      safeAccess = n.asExpr() and
      gc.controls(safeAccess.getBasicBlock(), true)
    )
  }

  override predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2) {
    exists(FunctionCall call | call.getTarget().hasName("append") |
      call.getArgument(0) = node1.asExpr() and
      call = node2.asExpr()
    )
  }
}

from MyConfig config, DataFlow::PathNode source, DataFlow::PathNode sink
where config.hasFlowPath(source, sink)
select sink, source, sink, "Insecure usage of sink"
