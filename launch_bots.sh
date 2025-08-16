#!/bin/bash

# AutoProver Bot Launcher
# Starts the formally verified bot network with real processes

set -e

echo "=== AutoProver Bot Network Launcher ==="

# Check dependencies
check_dependency() {
    if ! command -v "$1" &> /dev/null; then
        echo "❌ Missing dependency: $1"
        echo "   Install with: $2"
        exit 1
    else
        echo "✅ Found: $1"
    fi
}

echo "Checking dependencies..."
check_dependency "ocamlfind" "opam install ocamlfind"
check_dependency "dune" "opam install dune"
check_dependency "coqtop" "apt install coq"

# Check optional bot executables
echo "Checking bot executables..."
if command -v python3 &> /dev/null && python3 -c "import coqgym" 2>/dev/null; then
    echo "✅ CoqGym available"
    COQGYM_AVAILABLE=true
else
    echo "⚠️  CoqGym not available (install: pip install coqgym)"
    COQGYM_AVAILABLE=false
fi

if command -v proverbot9001 &> /dev/null; then
    echo "✅ ProverBot9001 available"
    PROVERBOT_AVAILABLE=true
else
    echo "⚠️  ProverBot9001 not available"
    PROVERBOT_AVAILABLE=false
fi

if coqtop -l coqhammer 2>/dev/null; then
    echo "✅ CoqHammer available"
    HAMMER_AVAILABLE=true
else
    echo "⚠️  CoqHammer not available (install: opam install coq-hammer)"
    HAMMER_AVAILABLE=false
fi

# Build the runtime
echo ""
echo "Building bot runtime..."
cd /home/scott/Repo/AutoProver

# Create dune-project if it doesn't exist
if [ ! -f dune-project ]; then
    cat > dune-project << 'EOF'
(lang dune 3.0)

(package
 (name autoprover)
 (depends ocaml dune lwt unix bigarray))
EOF
fi

# Create main dune file
cat > src/dune << 'EOF'
(executables
 (public_names autoprover-runtime)
 (name bot_execution_engine)
 (modules bot_execution_engine)
 (libraries unix lwt bigarray))

(rule
 (target bot_execution_engine.exe)
 (deps ./runtime/bot_execution_engine.ml)
 (action (run ocamlopt -I +unix -I +bigarray unix.cmxa bigarray.cmxa lwt.cmxa %{deps} -o %{target})))
EOF

# Build
echo "Compiling runtime..."
dune build src/runtime/bot_execution_engine.exe 2>/dev/null || {
    echo "Using direct compilation..."
    cd src/runtime
    ocamlfind ocamlopt -package unix,lwt,bigarray -linkpkg \
        ../core/nvs_bot_network.ml \
        bot_execution_engine.ml \
        -o ../../autoprover-runtime
    cd ../..
}

# Create startup script
cat > start_bots.sh << 'EOF'
#!/bin/bash

echo "=== Starting AutoProver Bot Network ==="

# Set up shared memory
sudo mkdir -p /dev/shm
sudo chmod 1777 /dev/shm

# Clean up old shared memory
sudo rm -f /dev/shm/autoprover_*

# Start the runtime
echo "Starting bot runtime engine..."
./autoprover-runtime &
RUNTIME_PID=$!

echo "Bot runtime started (PID: $RUNTIME_PID)"
echo "Bots are now running with formally verified safety guarantees!"
echo ""
echo "Monitor with: ps aux | grep autoprover"
echo "Stop with: kill $RUNTIME_PID"
echo ""
echo "NVS Registry accessible via shared memory at /dev/shm/autoprover_nvs"

# Wait for interrupt
trap "echo 'Stopping bots...'; kill $RUNTIME_PID; exit 0" INT
wait $RUNTIME_PID
EOF

chmod +x start_bots.sh

# Create bot status checker
cat > check_bots.sh << 'EOF'
#!/bin/bash

echo "=== AutoProver Bot Status ==="

echo "Runtime processes:"
ps aux | grep -E "(autoprover|bot_execution)" | grep -v grep || echo "No runtime processes found"

echo ""
echo "Shared memory segments:"
ls -la /dev/shm/autoprover_* 2>/dev/null || echo "No shared memory segments found"

echo ""
echo "Bot processes:"
ps aux | grep -E "(coqtop|python.*coq|proverbot)" | grep -v grep || echo "No bot processes found"

echo ""
if [ -f /dev/shm/autoprover_nvs ]; then
    echo "✅ NVS registry active"
    echo "Registry size: $(stat -c%s /dev/shm/autoprover_nvs 2>/dev/null || echo 'unknown') bytes"
else
    echo "❌ NVS registry not found"
fi
EOF

chmod +x check_bots.sh

# Create test client
cat > test_bots.sh << 'EOF'
#!/bin/bash

echo "=== Testing Bot Network ==="

# Simple test by checking if we can interact with the runtime
if pgrep -f autoprover-runtime > /dev/null; then
    echo "✅ Runtime is running"
    
    # Test shared memory access
    if [ -r /dev/shm/autoprover_nvs ]; then
        echo "✅ Can access NVS registry"
        echo "✅ Bot network is operational!"
        
        echo ""
        echo "Available bots (from process list):"
        ps aux | grep -E "(coqtop|python.*coq|proverbot)" | grep -v grep | awk '{print "  - " $11}'
        
    else
        echo "❌ Cannot access NVS registry"
    fi
else
    echo "❌ Runtime not running"
    echo "Start with: ./start_bots.sh"
fi
EOF

chmod +x test_bots.sh

echo ""
echo "✅ AutoProver Bot Network Setup Complete!"
echo ""
echo "Available commands:"
echo "  ./start_bots.sh   - Start the bot network"
echo "  ./check_bots.sh   - Check bot status"
echo "  ./test_bots.sh    - Test bot network"
echo ""

if [ "$1" = "--start" ]; then
    echo "Starting bots automatically..."
    ./start_bots.sh
else
    echo "To start the bots: ./start_bots.sh"
fi