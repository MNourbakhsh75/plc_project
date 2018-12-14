package main.symbolTable.symbolTableVariable;

import main.ast.Type.Type;
import main.ast.node.declaration.VarDeclaration;

public class SymbolTableLocalVariableItem extends SymbolTableVariableItemBase {
    public SymbolTableLocalVariableItem(String name , Type type , int index )
    {
        super( name , type , index );
    }
    public SymbolTableLocalVariableItem(VarDeclaration localVar )
    {
        super( localVar );
    }
}
