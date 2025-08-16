(*
 * Deployment Manager - Configure where and how to use the bot network
 *)

open Yojson.Safe.Util

(* ========== Configuration Types ========== *)

type resource_limits = {
  memory_mb: int;
  cpu_cores: int;
  timeout_sec: int;
}

type bot_config = {
  enabled: bool;
  path: string;
  args: string list;
  capabilities: string list;
  resource_limits: resource_limits;
}

type deployment_target = {
  description: string;
  enabled: bool;
  shared_memory_path: string;
  bot_instances: (string * int) list;
}

type usage_mode = {
  description: string;
  enabled: bool;
  parameters: (string * Yojson.Safe.t) list;
}

type deployment_config = {
  infrastructure: (string * Yojson.Safe.t) list;
  bot_executables: (string, bot_config) Hashtbl.t;
  deployment_targets: (string, deployment_target) Hashtbl.t;
  usage_modes: (string, usage_mode) Hashtbl.t;
}

(* ========== Configuration Loading ========== *)

module ConfigLoader = struct
  
  let load_resource_limits json =
    {
      memory_mb = json |> member "memory_mb" |> to_int;
      cpu_cores = json |> member "cpu_cores" |> to_int;
      timeout_sec = json |> member "timeout_sec" |> to_int;
    }
  
  let load_bot_config json =
    {
      enabled = json |> member "enabled" |> to_bool;
      path = json |> member "path" |> to_string;
      args = json |> member "args" |> to_list |> List.map to_string;
      capabilities = json |> member "capabilities" |> to_list |> List.map to_string;
      resource_limits = json |> member "resource_limits" |> load_resource_limits;
    }
  
  let load_deployment_target json =
    {
      description = json |> member "description" |> to_string;
      enabled = json |> member "enabled" |> to_bool;
      shared_memory_path = json |> member "shared_memory_path" |> to_string;
      bot_instances = 
        json |> member "bot_instances" |> to_assoc 
        |> List.map (fun (k, v) -> (k, to_int v));
    }
  
  let load_usage_mode json =
    {
      description = json |> member "description" |> to_string;
      enabled = json |> member "enabled" |> to_bool;
      parameters = json |> to_assoc;
    }
  
  let load_config_file path =
    let json = Yojson.Safe.from_file path in
    
    let bot_executables = Hashtbl.create 16 in
    json |> member "bot_executables" |> to_assoc |> List.iter (fun (name, config) ->
      Hashtbl.add bot_executables name (load_bot_config config)
    );
    
    let deployment_targets = Hashtbl.create 8 in
    json |> member "deployment_targets" |> to_assoc |> List.iter (fun (name, target) ->
      Hashtbl.add deployment_targets name (load_deployment_target target)
    );
    
    let usage_modes = Hashtbl.create 8 in
    json |> member "usage_modes" |> to_assoc |> List.iter (fun (name, mode) ->
      Hashtbl.add usage_modes name (load_usage_mode mode)
    );
    
    {
      infrastructure = json |> member "infrastructure" |> to_assoc;
      bot_executables;
      deployment_targets;
      usage_modes;
    }
end

(* ========== Deployment Manager ========== *)

module DeploymentManager = struct
  
  let config_ref = ref None
  
  let load_config ?(path="config/bot_deployment.json") () =
    let config = ConfigLoader.load_config_file path in
    config_ref := Some config;
    Printf.printf "[Deployment] Loaded configuration from %s\n" path;
    config
  
  let get_config () =
    match !config_ref with
    | Some config -> config
    | None -> failwith "Configuration not loaded. Call load_config() first."
  
  (* Get enabled bots for a deployment target *)
  let get_bots_for_target target_name =
    let config = get_config () in
    match Hashtbl.find_opt config.deployment_targets target_name with
    | Some target when target.enabled ->
        let bots = ref [] in
        List.iter (fun (bot_name, count) ->
          match Hashtbl.find_opt config.bot_executables bot_name with
          | Some bot_config when bot_config.enabled ->
              for i = 1 to count do
                bots := (bot_name ^ "_" ^ string_of_int i, bot_config) :: !bots
              done
          | _ -> Printf.printf "[Deployment] Bot %s not found or disabled\n" bot_name
        ) target.bot_instances;
        !bots
    | _ -> []
  
  (* Get deployment target configuration *)
  let get_target_config target_name =
    let config = get_config () in
    Hashtbl.find_opt config.deployment_targets target_name
  
  (* Check if a usage mode is enabled *)
  let is_usage_mode_enabled mode_name =
    let config = get_config () in
    match Hashtbl.find_opt config.usage_modes mode_name with
    | Some mode -> mode.enabled
    | None -> false
  
  (* Get usage mode parameters *)
  let get_usage_mode_params mode_name =
    let config = get_config () in
    match Hashtbl.find_opt config.usage_modes mode_name with
    | Some mode when mode.enabled -> Some mode.parameters
    | _ -> None
  
  (* Display configuration summary *)
  let show_config () =
    let config = get_config () in
    
    Printf.printf "\n=== AutoProver Deployment Configuration ===\n\n";
    
    Printf.printf "Bot Executables:\n";
    Hashtbl.iter (fun name bot_config ->
      let status = if bot_config.enabled then "✅" else "❌" in
      Printf.printf "  %s %s -> %s\n" status name bot_config.path;
      Printf.printf "    Capabilities: %s\n" (String.concat ", " bot_config.capabilities);
      Printf.printf "    Resources: %dMB RAM, %d cores, %ds timeout\n"
        bot_config.resource_limits.memory_mb
        bot_config.resource_limits.cpu_cores
        bot_config.resource_limits.timeout_sec;
    ) config.bot_executables;
    
    Printf.printf "\nDeployment Targets:\n";
    Hashtbl.iter (fun name target ->
      let status = if target.enabled then "✅" else "❌" in
      Printf.printf "  %s %s: %s\n" status name target.description;
      if target.enabled then (
        Printf.printf "    Shared memory: %s\n" target.shared_memory_path;
        Printf.printf "    Bot instances: %s\n" 
          (String.concat ", " (List.map (fun (b, c) -> Printf.sprintf "%s×%d" b c) target.bot_instances));
      );
    ) config.deployment_targets;
    
    Printf.printf "\nUsage Modes:\n";
    Hashtbl.iter (fun name mode ->
      let status = if mode.enabled then "✅" else "❌" in
      Printf.printf "  %s %s: %s\n" status name mode.description;
    ) config.usage_modes;
    
    Printf.printf "\n"
end

(* ========== Command Line Interface ========== *)

module CLI = struct
  
  let deploy_to_target target_name =
    Printf.printf "[Deployment] Deploying to target: %s\n" target_name;
    
    match DeploymentManager.get_target_config target_name with
    | Some target when target.enabled ->
        Printf.printf "[Deployment] Target: %s\n" target.description;
        Printf.printf "[Deployment] Shared memory: %s\n" target.shared_memory_path;
        
        let bots = DeploymentManager.get_bots_for_target target_name in
        Printf.printf "[Deployment] Starting %d bot instances:\n" (List.length bots);
        
        List.iter (fun (instance_name, bot_config) ->
          Printf.printf "  • %s: %s %s\n" 
            instance_name 
            bot_config.path 
            (String.concat " " bot_config.args);
        ) bots;
        
        (* Here you would actually start the bots using the runtime engine *)
        Printf.printf "[Deployment] Deployment complete!\n"
        
    | Some _ -> Printf.printf "[Deployment] Target %s is disabled\n" target_name
    | None -> Printf.printf "[Deployment] Target %s not found\n" target_name
  
  let use_mode mode_name params =
    Printf.printf "[Usage] Activating mode: %s\n" mode_name;
    
    if DeploymentManager.is_usage_mode_enabled mode_name then (
      match DeploymentManager.get_usage_mode_params mode_name with
      | Some mode_params ->
          Printf.printf "[Usage] Mode parameters:\n";
          List.iter (fun (key, value) ->
            Printf.printf "  %s: %s\n" key (Yojson.Safe.to_string value)
          ) mode_params;
          
          (* Merge in command-line params *)
          List.iter (fun param ->
            Printf.printf "[Usage] Override: %s\n" param
          ) params;
          
          Printf.printf "[Usage] Mode %s activated\n" mode_name
      | None -> Printf.printf "[Usage] Mode %s has no parameters\n" mode_name
    ) else
      Printf.printf "[Usage] Mode %s is not enabled\n" mode_name
  
  let main args =
    let config_path = ref "config/bot_deployment.json" in
    let target = ref None in
    let usage_mode = ref None in
    let usage_params = ref [] in
    let show_config = ref false in
    
    let rec parse_args = function
      | [] -> ()
      | "--config" :: path :: rest ->
          config_path := path;
          parse_args rest
      | "--deploy" :: target_name :: rest ->
          target := Some target_name;
          parse_args rest
      | "--use" :: mode_name :: rest ->
          usage_mode := Some mode_name;
          parse_args rest
      | "--param" :: param :: rest ->
          usage_params := param :: !usage_params;
          parse_args rest
      | "--show-config" :: rest ->
          show_config := true;
          parse_args rest
      | arg :: _ ->
          Printf.printf "Unknown argument: %s\n" arg;
          exit 1
    in
    
    parse_args args;
    
    (* Load configuration *)
    let _ = DeploymentManager.load_config ~path:!config_path () in
    
    (* Execute requested action *)
    if !show_config then
      DeploymentManager.show_config ()
    else (
      match !target with
      | Some target_name -> deploy_to_target target_name
      | None -> ()
    );
    
    match !usage_mode with
    | Some mode_name -> use_mode mode_name (List.rev !usage_params)
    | None -> ()
end

(* ========== Main Entry Point ========== *)

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  CLI.main args