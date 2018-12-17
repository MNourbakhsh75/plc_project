package main.visitor.typeAnalyzer;

import main.ast.node.Node;
import main.ast.node.Program;
import main.ast.node.declaration.ClassDeclaration;
import main.ast.node.declaration.MainMethodDeclaration;
import main.ast.node.declaration.MethodDeclaration;
import main.ast.node.declaration.VarDeclaration;
import main.ast.node.expression.*;
import main.ast.node.expression.BinOp.*;
import main.ast.node.expression.Value.BooleanValue;
import main.ast.node.expression.Value.IntValue;
import main.ast.node.expression.Value.StringValue;
import main.ast.node.statement.*;
import main.ast.Type.*;
import main.ast.Type.ArrayType.*;
import main.ast.Type.PrimitiveType.*;
import main.ast.Type.NoType.*;
import main.ast.Type.UserDefinedType.*;
import main.symbolTable.ClassSymbolTableItem;
import main.symbolTable.itemException.ItemNotFoundException;
import main.symbolTable.*;
import main.symbolTable.SymbolTable;
import main.symbolTable.SymbolTableMethodItem;
import main.symbolTable.symbolTableVariable.SymbolTableFieldVariableItem;
import main.symbolTable.symbolTableVariable.SymbolTableLocalVariableItem;
import main.symbolTable.symbolTableVariable.SymbolTableVariableItemBase;
import main.visitor.VisitorImpl;
import main.visitor.nameAnalyzer.*;
import java.util.*;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;


public class TypeAnalyzer extends VisitorImpl {
    private SymbolTableConstructor symConstructor;
    private TraverseState traverseState;
    private SymbolTableClassParentLinker symTableClassLinker;
    private ArrayList<String> nameErrors;
    private int lastIndexOfVariable;

    public TypeAnalyzer() {
        symConstructor = new SymbolTableConstructor();
        symTableClassLinker = new SymbolTableClassParentLinker();
        nameErrors = new ArrayList<>();
        lastIndexOfVariable = 0;
        setState(TraverseState.symbolTableConstruction);
    }

    public int numOfErrors() {
        return nameErrors.size();
    }

    private void switchState() {
        if (traverseState.name().equals(TraverseState.symbolTableConstruction.toString()))
            setState(TraverseState.redefinitionAndArrayErrorCatching);
        else if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())
                && nameErrors.size() != 0)
            setState(TraverseState.PrintError);
        else
            setState(TraverseState.Exit);
    }

    private void setState(TraverseState traverseState) {
        this.traverseState = traverseState;
    }

    private void checkForPropertyRedefinition(ClassDeclaration classDeclaration) {
        String name = classDeclaration.getName().getName();
        if (name.indexOf('$') != -1)
            nameErrors.add("Line:" + classDeclaration.getName().getLineNum() + ":Redefinition of class "
                    + name.substring(name.indexOf('$') + 1));
        try {
            ClassSymbolTableItem classItem = (ClassSymbolTableItem) SymbolTable.root
                    .getInCurrentScope(ClassSymbolTableItem.CLASS + name);
            SymbolTable next = classItem.getClassSym();
            SymbolTable.push(next);
        } catch (ItemNotFoundException itemNotFound) {
            System.out.println("there is an error in pushing class symbol table");
        }
    }

    private void checkForPropertyRedefinitionInParentScopes(VarDeclaration varDeclaration) {
        String name = varDeclaration.getIdentifier().getName();
        Set<SymbolTable> visitedSymbolTables = new HashSet<>();
        String variableKey = SymbolTableVariableItemBase.VARIABLE + name;
        SymbolTable current = SymbolTable.top.getPreSymbolTable();
        visitedSymbolTables.add(SymbolTable.top);
        while (current != null && !visitedSymbolTables.contains(current)) {
            visitedSymbolTables.add(current);
            try {
                current.getInCurrentScope(variableKey);
                SymbolTableVariableItemBase variable = (SymbolTableVariableItemBase) SymbolTable.top
                        .getInCurrentScope(variableKey);
                variable.setName("$" + variable.getName());
                SymbolTable.top.updateItemInCurrentScope(variableKey, variable);
                nameErrors.add("Line:" + varDeclaration.getIdentifier().getLineNum() + ":Redefinition of variable "
                        + name.substring(name.indexOf('$') + 1));
                return;
            } catch (ItemNotFoundException itemNotFound) {
                current = current.getPreSymbolTable();
            }
        }
    }

    private void checkForPropertyRedefinition(VarDeclaration varDeclaration) {
        String name = varDeclaration.getIdentifier().getName();
        if (name.indexOf('$') != -1) {
            nameErrors.add("Line:" + varDeclaration.getIdentifier().getLineNum() + ":Redefinition of variable "
                    + name.substring(name.indexOf('$') + 1));
            return;
        }
        try {
            SymbolTableVariableItemBase varItem = (SymbolTableVariableItemBase) SymbolTable.top
                    .getInCurrentScope(SymbolTableVariableItemBase.VARIABLE + name);
            varItem.setIndex(lastIndexOfVariable++);
            SymbolTable.top.updateItemInCurrentScope(SymbolTableVariableItemBase.VARIABLE + name, varItem);
            if (varItem instanceof SymbolTableFieldVariableItem)
                checkForPropertyRedefinitionInParentScopes(varDeclaration);
        } catch (ItemNotFoundException itemNotFound) {
            System.out.println("not important");
        }
    }

    private void checkForPropertyRedefinitionInParentScope(MethodDeclaration methodDeclaration) {
        String name = methodDeclaration.getName().getName();
        String methodKey = SymbolTableMethodItem.METHOD + name;
        SymbolTable current = SymbolTable.top.getPreSymbolTable();
        Set<SymbolTable> visitedSymbolTables = new HashSet<>();
        visitedSymbolTables.add(SymbolTable.top);
        while (current != null && !visitedSymbolTables.contains(current)) {
            visitedSymbolTables.add(current);
            try {
                current.getInCurrentScope(methodKey);
                SymbolTableMethodItem method = (SymbolTableMethodItem) SymbolTable.top.getInCurrentScope(methodKey);
                method.setName("$" + method.getName());
                SymbolTable.top.updateItemInCurrentScope(methodKey, method);
                nameErrors.add("Line:" + methodDeclaration.getName().getLineNum() + ":Redefinition of method "
                        + name.substring(name.indexOf('$') + 1));
                return;
            } catch (ItemNotFoundException itemNotFound) {
                current = current.getPreSymbolTable();
            }
        }
    }

    private void checkForPropertyRedefinition(MethodDeclaration methodDeclaration) {
        String name = methodDeclaration.getName().getName();
        SymbolTable next = null;
        String methodKey = SymbolTableMethodItem.METHOD + name;
        try {
            next = ((SymbolTableMethodItem) SymbolTable.top.getInCurrentScope(methodKey)).getMethodSymbolTable();
        } catch (ItemNotFoundException itemNotFound) {
            System.out.println("an error occurred in pushing method symbol table");
            return;
        }
        if (name.indexOf('$') != -1) {
            nameErrors.add("Line:" + methodDeclaration.getName().getLineNum() + ":Redefinition of method "
                    + name.substring(name.indexOf('$') + 1));
            SymbolTable.push(next);
            return;
        }
        checkForPropertyRedefinitionInParentScope(methodDeclaration);
        SymbolTable.push(next);
    }
    
    private void checkForUndefinedVar(Expression expression) {
        // String[] nameArr = expression.toString().split(" ",-2);
        // String name = nameArr[1];
        // System.out.println("expression : " + name);
        // boolean checked = false;
        // HashMap <String, SymbolTableItem> hm = SymbolTable.top.getSymItems();
        // for (String value : hm.keySet()) {
        //     String[] arrOfStr = value.split("_", -2);
        //     System.out.println(arrOfStr[1]);
        //     if(arrOfStr[1].equals(name))
        //         checked = true;
        // }
        // if (!checked) {
        //     // if (name.indexOf('$') != -1) {
        //     nameErrors.add("Line:" + expression.getLineNum() + ":variable " + name + " is not declared");
        //     return;
        //     // }
        // }
    }
    
    private boolean checkForUndefinedType(VarDeclaration varDeclaration) {
        String name = varDeclaration.getIdentifier().getName();
        Type type = varDeclaration.getType();
        boolean checked = false;
        if( !((type instanceof ArrayType) || (type instanceof IntType) || (type instanceof BooleanType) || (type instanceof StringType)))
        {
            if ((type instanceof UserDefinedType)){
                HashMap <String, SymbolTableItem> hm = SymbolTable.root.getSymItems();
                for (SymbolTableItem value : hm.values()) {
                    ClassSymbolTableItem classItem = (ClassSymbolTableItem) value;
                    String className = classItem.getClassDeclaration().getName().getName();
                    if(className.equals(type.toString())){
                        checked = true;
                    }
                }
            }
            if (!checked){
                // if (name.indexOf('$') != -1) {
                    nameErrors.add("Line:" + varDeclaration.getIdentifier().getLineNum() +
                    ":Undefined Type For Variable "
                    + name.substring(name.indexOf('$') + 1));
                    // return;
                // }
            }
        } 
        return checked;       
    }
    private boolean checkForAssign(Assign assign){
        boolean checked = false;
        if (assign.getlValue().getType().toString().equals(assign.getrValue().getType().toString())){
            checked = true;
        } else if ((assign.getrValue().getType() instanceof NoType) && (!(assign.getlValue().getType() instanceof NoType))){
            checked = true;
        } else if ((assign.getlValue().getType() instanceof NoType) && (!(assign.getrValue().getType() instanceof NoType))){
            checked = false;
        }else if ((assign.getlValue().getType() instanceof ArrayType) && ((assign.getrValue().getType() instanceof NoType))) {
            checked = true;
        }else if ((assign.getlValue().getType() instanceof ArrayType) && ((assign.getrValue().getType() instanceof IntType))){
            checked = true;
        }else if ((assign.getlValue().getType() instanceof ArrayType) && ((assign.getrValue().getType() instanceof IntType))){
            checked = true;
        }else if (((assign.getlValue().getType() instanceof UserDefinedType)) && ((assign.getrValue().getType() instanceof UserDefinedType))) {
            String name1 = "Class_" + assign.getrValue().getType().toString();
            String name2 = "Class_" + assign.getlValue().getType().toString();
            HashMap<String, SymbolTableItem> hm = SymbolTable.root.getSymItems();
            if ((hm.containsKey(name1)) && (hm.containsKey(name2))){
                ClassSymbolTableItem classItem1 = (ClassSymbolTableItem) hm.get(name1);
                // ClassSymbolTableItem classItem2 = (ClassSymbolTableItem) hm.get(name2);
                String pName = classItem1.getParentName();
                if(pName != null){
                    while (pName != null){
                        if(pName.equals(assign.getlValue().getType().toString())){
                                checked = true;
                                break;
                        }else{
                            String tempName = "Class_" + pName;
                            ClassSymbolTableItem classItem2 = (ClassSymbolTableItem) hm.get(tempName);
                            pName = classItem2.getParentName();
                            if (pName == null){
                                checked = false;
                                break;
                            }
                        }
                    }
                }else{
                    checked = false;
                }
            }
        }else {
            checked = false;
        }
        return checked;
    }
    @Override
    public void visit(Node node) {
        // TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(Program program) {
        // TODO: implement appropriate visit functionality
        while (!traverseState.toString().equals(TraverseState.Exit.toString())) {
            // System.out.println("traverseState : " + traverseState.toString());
            if (traverseState.name().equals(TraverseState.symbolTableConstruction.toString()))
                symConstructor.constructProgramSym();
            else if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString()))
                symTableClassLinker.findClassesParents(program);
            else if (traverseState.name().equals(TraverseState.PrintError.toString())) {
                for (String error : nameErrors)
                    System.out.println(error);
                return;
            }
            this.visit(program.getMainClass());
            for (ClassDeclaration classDeclaration : program.getClasses())
                this.visit(classDeclaration);
            switchState();
        }
    }

    @Override
    public void visit(ClassDeclaration classDeclaration) {
        // TODO: implement appropriate visit functionality
        if (classDeclaration == null)
            return;
        if (traverseState.name().equals(TraverseState.symbolTableConstruction.toString()))
            symConstructor.construct(classDeclaration);
        else if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString()))
            checkForPropertyRedefinition(classDeclaration);
        // visitExpr(classDeclaration.getName());
        // visitExpr(classDeclaration.getParentName());
        for (VarDeclaration varDeclaration : classDeclaration.getVarDeclarations())
            this.visit(varDeclaration);
        for (MethodDeclaration methodDeclaration : classDeclaration.getMethodDeclarations())
            this.visit(methodDeclaration);
        SymbolTable.pop();
    }

    @Override
    public void visit(MethodDeclaration methodDeclaration) {
        // TODO: implement appropriate visit functionality
        if (methodDeclaration == null)
            return;
        if (traverseState.name().equals(TraverseState.symbolTableConstruction.toString()))
            symConstructor.construct(methodDeclaration);
        else if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString()))
            checkForPropertyRedefinition(methodDeclaration);
        for (VarDeclaration argDeclaration : methodDeclaration.getArgs())
            visit(argDeclaration);
        for (VarDeclaration localVariable : methodDeclaration.getLocalVars()) {
            this.visit(localVariable);
        }
        for (Statement statement : methodDeclaration.getBody())
            visitStatement(statement);
        visitExpr(methodDeclaration.getReturnValue());
        SymbolTable.pop();
        if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())){
            if (!(methodDeclaration.getReturnValue().getType() instanceof NoType))
                if(!(methodDeclaration.getReturnValue().getType().toString().equals(methodDeclaration.getActualReturnType().toString()))){
                    nameErrors.add("Line:" + methodDeclaration.getReturnValue().getLineNum() + ": "+methodDeclaration.getName().getName()+" return type must be " + methodDeclaration.getActualReturnType().toString());                        
                }
        }
    }

    @Override
    public void visit(MainMethodDeclaration mainMethodDeclaration) {
        // TODO: implement appropriate visit functionality
        if (mainMethodDeclaration == null)
            return;
        if (traverseState.name().equals(TraverseState.symbolTableConstruction.toString()))
            visit((MethodDeclaration) mainMethodDeclaration);
        else if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString()))
            visit((MethodDeclaration) mainMethodDeclaration);
        for (Statement statement : mainMethodDeclaration.getBody())
            visitStatement(statement);
        visitExpr(mainMethodDeclaration.getReturnValue());
    }

    @Override
    public void visit(VarDeclaration varDeclaration) {
        // TODO: implement appropriate visit functionality
        if (varDeclaration == null)
        return;
        visitExpr(varDeclaration.getIdentifier());
        if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())){
            // checkForPropertyRedefinition(varDeclaration);
            // if(!checkForUndefinedType(varDeclaration))
                // varDeclaration.setType(new NoType());
            // System.out.println("var type :" + varDeclaration.getType());
        }
    }

    @Override
    public void visit(ArrayCall arrayCall) {
        // TODO: implement appropriate visit functionality
        if (arrayCall == null)
            return;
        try {
            visitExpr(arrayCall.getInstance());
            visitExpr(arrayCall.getIndex());
            if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())){
                int arrSize =((ArrayType)(arrayCall.getInstance().getType())).getSize();
                arrayCall.setType(new IntType());
                if((((IntValue)arrayCall.getIndex()).getConstant() > arrSize) || (((IntValue)arrayCall.getIndex()).getConstant() < 0)){
                    nameErrors.add("Line:" + arrayCall.getInstance().getLineNum() + ": invalid index for array");    
                }
            }
        } catch (NullPointerException npe) {
            System.out.println("instance or index is null");
        }

    }

    @Override
    public void visit(BinaryExpression binaryExpression) {
        // TODO: implement appropriate visit functionality
        if (binaryExpression == null)
            return;
        Expression lOperand = binaryExpression.getLeft();
        Expression rOperand = binaryExpression.getRight();
        BinaryOperator op = binaryExpression.getBinaryOperator();
        try {
            visitExpr(lOperand);
            visitExpr(rOperand);
            if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())) {
                if((op.name().equals("and")) || (op.name().equals("or"))){
                if ((lOperand.getType() instanceof BooleanType) && (rOperand.getType() instanceof BooleanType)){
                    binaryExpression.setType(lOperand.getType());
                }else{
                    binaryExpression.setType(new NoType());
                    nameErrors.add("Line:" + binaryExpression.getLineNum() + ": unsupported operand type for " + op.name());
                    // return; 
                }
            }else if ((op.name().equals("add")) || (op.name().equals("sub")) || (op.name().equals("mult")) || (op.name().equals("div"))){
                if ((lOperand.getType() instanceof IntType) && (rOperand.getType() instanceof IntType)) {
                    binaryExpression.setType(lOperand.getType());
                } else if ((lOperand.getType() instanceof NoType) && (rOperand.getType() instanceof IntType)){
                    binaryExpression.setType(rOperand.getType());
                }else if ((lOperand.getType() instanceof IntType) && (rOperand.getType() instanceof NoType)){
                    binaryExpression.setType(lOperand.getType());
                }else if ((lOperand.getType() instanceof NoType) && (rOperand.getType() instanceof NoType)){
                    binaryExpression.setType(lOperand.getType());
                }
                else {
                    binaryExpression.setType(new NoType());
                    nameErrors.add("Line:" + binaryExpression.getLineNum() + ": unsupported operand type for " + op.name());
                    // return;
                }
            }else if ((op.name().equals("gt")) || (op.name().equals("lt")) || (op.name().equals("gte")) || (op.name().equals("lte"))){
                    if ((lOperand.getType() instanceof IntType) && (rOperand.getType() instanceof IntType)) {
                        binaryExpression.setType(new BooleanType());
                    } else if ((lOperand.getType() instanceof NoType) && (rOperand.getType() instanceof IntType)) {
                        binaryExpression.setType(new BooleanType());
                    } else if ((lOperand.getType() instanceof IntType) && (rOperand.getType() instanceof NoType)) {
                        binaryExpression.setType(new BooleanType());
                    } else if ((lOperand.getType() instanceof NoType) && (rOperand.getType() instanceof NoType)) {
                        binaryExpression.setType(new BooleanType());
                    }else{
                        binaryExpression.setType(new NoType());
                        nameErrors.add("Line:" + binaryExpression.getLineNum() + ": unsupported operand type for " + op.name());
                    }
            }else if ((op.name().equals("eq")) || (op.name().equals("neq"))){
                if ((lOperand.getType().toString().equals(rOperand.getType().toString()))){
                    binaryExpression.setType(new BooleanType());
                }else if ((rOperand.getType() instanceof NoType) && !(lOperand.getType() instanceof NoType)){
                    binaryExpression.setType(new BooleanType());
                }
            }
            }
        } catch (NullPointerException npe) {
            System.out.println("one of operands is null, there is a syntax error");
        }
    }

    @Override
    public void visit(Identifier identifier) {
        // TODO: implement appropriate visit functionality
        // System.out.println("iii : " + identifier.getName());
        if (identifier == null)
            return;
        if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())) {
            // String[] nameArr = assign.getlValue().toString().split(" ", -2);
            String name = "Variable_" + identifier.getName();
            try {
                SymbolTableVariableItemBase si = (SymbolTableVariableItemBase) SymbolTable.top.get(name);
                identifier.setType(si.getType());
            } catch (ItemNotFoundException itemNotFoundException) {
                identifier.setType(new NoType());
                nameErrors.add(
                        "Line:" + identifier.getLineNum() + ": variable " + identifier.getName() + " is not declared");
                // return;
            }
        }
    }

    @Override
    public void visit(Length length) {
        // TODO: implement appropriate visit functionality
        if (length == null)
            return;
        visitExpr(length.getExpression());
        if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())) {
            if ((length.getExpression().getType() instanceof ArrayType) || (length.getExpression().getType() instanceof NoType)){
                length.setType(new IntType());
            }else{
                length.setType(new NoType());
                nameErrors.add("Line:" + length.getLineNum() + ": length is only for array type");
            }
        }

    }

    @Override
    public void visit(MethodCall methodCall) {
        if (methodCall == null)
            return;        
        try {
            // visitExpr(methodCall.getInstance());
            // visitExpr(methodCall.getMethodName());
            // System.out.println("Method ins : " + methodCall.getInstance() + " Line "+ methodCall.getInstance().getLineNum());
            // if(methodCall.getArgs() != null){
                for (Expression argument : methodCall.getArgs())
                    visitExpr(argument);
            // }
            if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())){
                String name;
                if (methodCall.getInstance() instanceof NewClass){
                    visitExpr(methodCall.getInstance());
                    name = "Class_" + ((NewClass)methodCall.getInstance()).getClassName().getType().toString();
                }else{
                    String varName = "Variable_" + ((Identifier) methodCall.getInstance()).getName();
                    try {
                        SymbolTableVariableItemBase si = (SymbolTableVariableItemBase) SymbolTable.top.get(varName);
                        (methodCall.getInstance()).setType(si.getType());
                    } catch (ItemNotFoundException itemNotFoundException) {
                        (methodCall.getInstance()).setType(new NoType());
                        nameErrors.add("Line:" + methodCall.getInstance().getLineNum() + ": variable "
                                + ((Identifier) methodCall.getInstance()).getName() + " is not declared");
                        // return;
                    }
                    name = "Class_" + methodCall.getInstance().getType().toString();
                }
                String[] nameArr = name.split("_",-2);
                try {
                    ClassSymbolTableItem sti = (ClassSymbolTableItem) SymbolTable.top.get(name);
                    try {
                        String methodName = "Method_" + methodCall.getMethodName().getName();
                        SymbolTable classSymbolTable = sti.getClassSym();
                        SymbolTableMethodItem methodNames = (SymbolTableMethodItem) classSymbolTable.get(methodName);
                        ArrayList<VarDeclaration> methodArgs = (methodNames.getMethodDeclaration()).getArgs();
                        ArrayList<Expression> methodCallArgs = methodCall.getArgs();
                        int methodArgsSize = methodArgs.size();
                        int methodCallArgsSize = methodCallArgs.size();
                        if (methodCallArgsSize != methodArgsSize){
                            nameErrors.add("Line:"+methodCall.getInstance().getLineNum()+": Unmatch Args for method "+ methodCall.getMethodName().getName());
                        }
                        if(methodCallArgsSize <= methodArgsSize ){
                            for(int i =0 ;i < methodCallArgsSize;i++){
                                if ((!(methodCallArgs.get(i).getType() instanceof NoType)))
                                    if ((!(methodCallArgs.get(i).getType().toString().equals(methodArgs.get(i).getType().toString())))){
                                        nameErrors.add("Line:"+methodCall.getInstance().getLineNum()+": Unmatch Args Type for "+ ((Identifier)methodCallArgs.get(i)).getName() + " in method "+ methodCall.getMethodName().getName());
                                    }
                            }
                        }
                        if (methodCallArgsSize > methodArgsSize){
                            for(int i =0 ;i < methodArgsSize;i++){
                                    if ((!(methodCallArgs.get(i).getType() instanceof NoType)))
                                        if ((!(methodCallArgs.get(i).getType().toString().equals(methodArgs.get(i).getType().toString())))){
                                            nameErrors.add("Line:"+methodCall.getInstance().getLineNum()+": Unmatch Args Type for "+ ((Identifier)methodCallArgs.get(i)).getName() + " in method "+ methodCall.getMethodName().getName());
                                        }
                            }
                        }
                        methodCall.setType(methodNames.getMethodDeclaration().getActualReturnType());
                    } catch (ItemNotFoundException itemNotFoundException2) {
                        methodCall.setType(new NoType());
                        nameErrors.add("Line:"+ methodCall.getInstance().getLineNum()+": there is no method named "+ methodCall.getMethodName().getName() + " in class " +nameArr[1]);
                    }

                } catch (ItemNotFoundException itemNotFoundException) {
                    methodCall.setType(new NoType());
                    nameErrors.add("Line:"+ methodCall.getInstance().getLineNum()+": class "+ nameArr[1] + " is not declared");
                    // return;
                }
            }
        } catch (NullPointerException npe) {
            System.out.println("syntax error occurred");
        }
        // TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(NewArray newArray) {
        // TODO: implement appropriate visit functionality
        if (newArray == null)
            return;
        visitExpr(newArray.getExpression());
        if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())){
            ArrayType art = new ArrayType();
            art.setSize(((IntValue)newArray.getExpression()).getConstant());
            newArray.setType(art);
        }
    }

    @Override
    public void visit(NewClass newClass) {
        // TODO: implement appropriate visit functionality
        if (newClass == null)
            return;
        // visitExpr(newClass.getClassName());
        if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())){
            // System.out.println("newClass name " + newClass.getClassName().getName());
            // System.out.println("newClass type " + newClass.getClassName().getType().toString());
            String name = "Class_" + newClass.getClassName().getName();
            try {
                ClassSymbolTableItem sti = (ClassSymbolTableItem) SymbolTable.top.get(name);
                UserDefinedType newType = new UserDefinedType();
                newType.setName(sti.getClassDeclaration().getName());
                newClass.getClassName().setType(newType);
                newClass.setType(newType);
            } catch (ItemNotFoundException itemNotFoundException) {
                nameErrors.add("Line:" + newClass.getClassName().getLineNum() + ": class "
                        + newClass.getClassName().getName() + " is not declared");
                // return;
            }
        }
    }

    @Override
    public void visit(This instance) {
        // TODO: implement appropriate visit functionality
        System.out.println("instance : " + instance);

        // if(instance == null)
        //     return;
        // if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())){
        //     System.out.println("instance : "+instance);

        // }        
    }

    @Override
    public void visit(UnaryExpression unaryExpression) {
        // TODO: implement appropriate visit functionality
        if (unaryExpression == null)
            return;
        UnaryOperator op = unaryExpression.getUnaryOperator();
        try {
            visitExpr(unaryExpression.getValue());
            if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())){
                if((op.name().equals("minus"))){
                    if ((unaryExpression.getValue().getType() instanceof IntType)){
                        unaryExpression.setType(unaryExpression.getValue().getType());
                    }else if ((unaryExpression.getValue().getType() instanceof NoType)) {
                        unaryExpression.setType(unaryExpression.getValue().getType());
                    }else{
                        unaryExpression.setType(new NoType());
                        nameErrors.add("Line:" + unaryExpression.getLineNum() + ": unsupported operand type for " + op.name());
                        // return; 
                    }
                }
                if ((op.name().equals("not"))) {
                    if ((unaryExpression.getValue().getType() instanceof BooleanType)) {
                        unaryExpression.setType(unaryExpression.getValue().getType());
                    } else if ((unaryExpression.getValue().getType() instanceof NoType)) {
                        unaryExpression.setType(unaryExpression.getValue().getType());
                    }else {
                        unaryExpression.setType(new NoType());
                        nameErrors.add("Line:" + unaryExpression.getLineNum() + ": unsupported operand type for " + op.name());
                        // return;
                    }
                }
            }            
        } catch (NullPointerException npe) {
            System.out.println("unary value is null");
        }
    }

    @Override
    public void visit(BooleanValue value) {
        // TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(IntValue value) {
        // TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(StringValue value) {
        // TODO: implement appropriate visit functionality
    }

    @Override
    public void visit(Assign assign) {
        // TODO: implement appropriate visit functionality
        if (assign == null)
            return;
        try {
            Expression lExpr = assign.getlValue();
            visitExpr(lExpr);
            Expression rValExpr = assign.getrValue();
            if (rValExpr != null)
                visitExpr(rValExpr);
            if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())) {
                // System.out.println("lAssign : " + lExpr.getType().toString()+ " : " + assign.getLineNum());
                // System.out.println("rAssign : " + rValExpr.getType().toString() + " : "+ assign.getLineNum());
                if(!(lExpr instanceof Identifier)){
                    if(!(lExpr instanceof ArrayCall)){
                        nameErrors.add("Line:" + assign.getLineNum() + ": left side of assignment must be a valid lvalue");
                    }
                }else{
                    if (!checkForAssign(assign))
                        nameErrors.add("Line:" + assign.getLineNum() + ": invalid assgin");
                }
                if ((assign.getlValue().getType() instanceof ArrayType) && ((assign.getrValue().getType() instanceof ArrayType))){
                    int size = ((ArrayType)assign.getrValue().getType()).getSize();
                    ((ArrayType)assign.getlValue().getType()).setSize(size);
                }
                

            }            
        } catch (NullPointerException npe) {
            System.out.println("lvalue expression is null");
        }
    }

    @Override
    public void visit(Block block) {
        // TODO: implement appropriate visit functionality
        if (block == null)
            return;
        for (Statement blockStat : block.getBody())
            this.visitStatement(blockStat);
    }

    @Override
    public void visit(Conditional conditional) {
        // TODO: implement appropriate visit functionality
        if (conditional == null)
            return;

        visitExpr(conditional.getExpression());
        visitStatement(conditional.getConsequenceBody());
        visitStatement(conditional.getAlternativeBody());
        if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())) {
            if (!(conditional.getExpression().getType() instanceof BooleanType)){
                nameErrors.add("Line:" + conditional.getExpression().getLineNum() + ": condition type must be boolean");
            }
        }
    }

    @Override
    public void visit(While loop) {
        // TODO: implement appropriate visit functionality
        if (loop == null)
            return;
        visitExpr(loop.getCondition());
        visitStatement(loop.getBody());
        if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())) {
            if (!(loop.getCondition().getType() instanceof BooleanType)){
                nameErrors.add("Line:" + loop.getCondition().getLineNum() + ": condition type must be boolean");
            }
        }

    }

    @Override
    public void visit(Write write) {
        // TODO: implement appropriate visit functionality
        if (write == null)
            return;

        visitExpr(write.getArg());
        if (traverseState.name().equals(TraverseState.redefinitionAndArrayErrorCatching.toString())) {
            if (!(write.getArg().getType() instanceof IntType) && !(write.getArg().getType() instanceof StringType) && !(write.getArg().getType() instanceof ArrayType)){
                nameErrors.add("Line:"+ write.getLineNum()+": unsupported type for writeln");
            }


        }
    }
}
