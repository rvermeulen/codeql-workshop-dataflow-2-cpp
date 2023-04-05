/**
 * @kind path-problem
 */

 import cpp
 import semmle.code.cpp.dataflow.new.DataFlow
 import semmle.code.cpp.controlflow.Guards

 // Predicate used to limit the exploration of our partial path graph
 // to 3 inter procedural steps.
 // That is, it won't include steps 4 function calls away from the source.
 // The exploration limit is required to make the computation tractable and should be adjusted
 // when the current limit doesn't provide insight into a missing flow.
 int explorationLimit() {
    result = 3
 }
 module MyDataFlow = DataFlow::Make<MyConfig>;

 // Here we create our own `FlowExploration` module configured with the predicate `explorationLimit`
 // that adheres to the predicate signature `signature int explorationLimitSig();`
 // The syntax `<explorationLimit/0>` refers to a predicate and its cardinality.
 module MyFlowExploration = MyDataFlow::FlowExploration<explorationLimit/0>;
 import MyFlowExploration::PartialPathGraph

 module MyConfig implements DataFlow::ConfigSig {
 
     predicate isSource(DataFlow::Node n) {
         exists(FunctionCall call | call.getTarget().hasName("source1") |
             n.asIndirectExpr() = call
         )
         or
         exists(FunctionCall call | call.getTarget().hasName("source2") |
             call.getArgument(0) = n.asDefiningArgument()
         )
     }
 
     predicate isSink(DataFlow::Node n) {
         exists(FunctionCall call | call.getTarget().hasName("sink") |
             call.getAnArgument() = n.asIndirectArgument(1)
         )
     }
 
     predicate isBarrier(DataFlow::Node n) {
         exists(FunctionCall call| call.getTarget().hasName("sanitize") |
             call.getAnArgument() = n.asIndirectArgument()
         )
         or
         exists(GuardCondition gc, FunctionCall call, Variable v, VariableAccess safeAccess | 
             call.getTarget().hasName("valid") and gc = call |
 
             call.getAnArgument() = v.getAnAccess() and
             safeAccess = v.getAnAccess() and
             safeAccess = n.asIndirectExpr() and
             gc.controls(safeAccess.getBasicBlock(), true)
         )
     }
 }
 
 // Here we use our flow exploration module to find partial flows with a distance >= 1.
 // The distance is between 0 and our exploration limit, and indicates the number of inter procedural steps required
 // to reach `n` from the source.
 from MyFlowExploration::PartialPathNode source, MyFlowExploration::PartialPathNode n, int dist
 where MyFlowExploration::hasPartialFlow(source, n, dist) and dist >= 1
 select n.getNode(), source, n, "n is " + dist + " inter procedural steps away from source"