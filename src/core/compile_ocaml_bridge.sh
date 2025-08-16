#!/bin/bash

echo "🔗 Compiling OCaml-Python Bridge for Maximum Parallelism"

cd /home/scott/Repo/AutoProver/src/core

# Compile the OCaml bridge
echo "Compiling OCaml bridge..."
ocamlc -I +unix unix.cma -o ocaml_python_bridge ocaml_python_bridge.ml

if [ $? -eq 0 ]; then
    echo "✅ OCaml bridge compiled successfully"
    echo "🚀 Testing parallel execution..."
    
    # Test the bridge
    ./ocaml_python_bridge
    
    echo ""
    echo "📋 Usage:"
    echo "  ./ocaml_python_bridge                    # Test mode"
    echo "  echo 'goal' | ./ocaml_python_bridge     # Pipe goal from stdin"
    echo ""
    echo "🔥 OCaml now coordinates ALL Python bot execution with TRUE parallelism!"
    
else
    echo "❌ OCaml compilation failed"
    echo "💡 Install OCaml with: sudo apt install ocaml"
    exit 1
fi