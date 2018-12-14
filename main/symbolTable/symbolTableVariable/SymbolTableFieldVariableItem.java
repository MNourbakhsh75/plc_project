package main.symbolTable.symbolTableVariable;

import main.ast.Type.Type;
import main.ast.node.declaration.VarDeclaration;

public class SymbolTableFieldVariableItem extends SymbolTableVariableItemBase {
    public SymbolTableFieldVariableItem(String name , Type type , int index )
    {
        super( name , type , index );
    }
    public SymbolTableFieldVariableItem(VarDeclaration field )
    {
        super( field );
    }
}
