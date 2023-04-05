/**
 * @kind path-problem
 */

 import cpp
 import semmle.code.cpp.dataflow.new.DataFlow
 import semmle.code.cpp.controlflow.Guards

 // Here we create a specialized data flow module based on our signature.
 // This uses the new parameterized modules functionality.
 // In version 0.6.1 of 'codeql/cpp-all' the data flow module is created using `DataFlow::Make`.
 // From version > 0.6.1 this will become `DataFlow::Global`.
 module MyDataFlow = DataFlow::Make<MyConfig>;
 // Import `PathGraph` from our data flow module to introduces the `edges` predicate used
 // to construct the paths between sources and sinks.
 import MyDataFlow::PathGraph

 // Define our configuration module implementing the `DataFlow::ConfigSig` module signature
 // stating which predicates need to be implemented.
 // The `isSource` and `isSink` are mandatory.
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
 
     predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2 ) {
        exists(FunctionCall call | call.getTarget().hasName("append") |
            call.getArgument(0) = node1.asIndirectArgument() and
            call = node2.asIndirectExpr()
        )
    }
 }
 
 // Use our data flow module to establish a flow between a source and a sink.
 // We no longer need a configuration class.
 from MyDataFlow::PathNode source, MyDataFlow::PathNode sink
 where MyDataFlow::hasFlowPath(source, sink)
 select sink, source, sink, "Insecure usage of sink"