library(ggplot2)
library(dplyr)
library(tidyr)
library(here)
library(nflfastR)
library(lme4)
library(glmnet)
library(gt)
library(gtsummary)
library(gtExtras)
library(stringdist)
library(fuzzyjoin)
library(caret)
library(xgboost)
library(pbapply)
library(ggridges)
library(XML)
library(RCurl)
library(stringr)
library(rlist)
library(ggpubr)

# Calculate the expected positional loss from the first turn to all 216 turns.
calculate_all_EPL <- function(draft_board) {
  ret <- draft_board  %>% filter(position_name != "FB") %>% 
    dplyr::select(player_name, projection_adp, total_fantasy_points, position_name) %>%
    # Set ADP to integers for distributions
    mutate(projection_adp = ceiling(projection_adp)) %>%
    group_by(position_name) %>%
    ungroup() %>%
    # Merge in cumulative pick probabilties by ADP
    left_join(general_pick_probs_by_adp, by = c("projection_adp")) %>%
    group_by(theoretical_pick_number, position_name) %>%
    # Order by true positional value (i.e. fantasy points)
    arrange(theoretical_pick_number, position_name, desc(total_fantasy_points)) %>%
    # Calculate the probability that all more valuable positional players are picked
    mutate(prob_all_higher_ranked_positional_players_picked = cumprod(dplyr::lag(prob_picked, default = 1))) %>%
    ungroup() %>%
    # Calculate the probability a player is best at his position on current turn
    mutate(prob_player_is_best_at_pos= (1-prob_picked)*prob_all_higher_ranked_positional_players_picked) %>%
    # Calculate expected max positional value at turn
    mutate(player_expected_value_if_best = total_fantasy_points*prob_player_is_best_at_pos) %>% 
    group_by(theoretical_pick_number, position_name) %>%
    mutate(expected_max_available_value_at_position = sum(player_expected_value_if_best)) %>% 
    ungroup() %>%
    # Subtract each players fantasy points from max positional value on every turn
    mutate(EPL_for_player = total_fantasy_points - expected_max_available_value_at_position) %>%
    group_by(theoretical_pick_number, position_name) %>%
    # Calculate EPL as expected positional loss on each turn compared to best positional player on turn 1
    # Also calculate expected and possible best positional players available at each turn
    mutate(EPL = max(total_fantasy_points) - expected_max_available_value_at_position,
           expected_best_available_player_at_position = paste0(player_name[which.max(prob_player_is_best_at_pos)][1], ' (', 
                                                               round(max(prob_player_is_best_at_pos)[1]*100,2), '%)'),
           possible_best_available_player_at_position_upper = 
             paste0(player_name[prob_player_is_best_at_pos > 0.1 & total_fantasy_points==max(total_fantasy_points[prob_player_is_best_at_pos > 0.1])][1], ' (', 
                    round(prob_player_is_best_at_pos[prob_player_is_best_at_pos > 0.1 & 
                                                       total_fantasy_points==max(total_fantasy_points[prob_player_is_best_at_pos > 0.1])][1]*100,2), '%)')) %>%
    ungroup() %>%
    group_by(theoretical_pick_number) %>%
    # Calculate best EPL pick looking N turns ahead from first pick
    mutate(EPL_positional_selection = position_name[which.max(EPL)][1],
           EPL_player_selection = player_name[which.max(EPL)][1]) %>%
    ungroup() %>%
    dplyr::select(theoretical_pick_number, player_name, position_name, 
                  projection_adp, total_fantasy_points, EPL_for_player, prob_player_is_best_at_pos, prob_picked, EPL, expected_best_available_player_at_position,
                  possible_best_available_player_at_position_upper, expected_max_available_value_at_position, EPL_positional_selection, EPL_player_selection)
  return(ret)
}

calculate_turns_until_next_pick <- function(current_turn, num_in_draft, limit = TRUE) {
  # Define logic to determine current snake direction
  snake_direction <- case_when((current_turn / num_in_draft) %% 2 == 1 ~ "up",
                               (current_turn / num_in_draft) %% 2 == 0 ~ "down",
                               ((floor(current_turn / num_in_draft) %% 2) == 0) & !((current_turn / num_in_draft) %% 2  %in% c(0, 1)) ~ "up", 
                               (floor(current_turn / num_in_draft) %% 2) == 1  & !((current_turn / num_in_draft) %% 2  %in% c(0, 1)) ~ "down")
  # Define logic to determine which pick order current drafter is
  pick_order <- case_when((snake_direction == "up") & ((current_turn %% num_in_draft) != 0) ~ (current_turn %% num_in_draft), 
                          (snake_direction == "down") & ((current_turn %% num_in_draft) != 0) ~ 1+(num_in_draft - (current_turn %% num_in_draft)),
                          (snake_direction == "up") & ((current_turn %% num_in_draft) == 0) ~ as.numeric(num_in_draft),
                          (snake_direction == "down") & ((current_turn %% num_in_draft) == 0) ~ 1)
  # Define logic to calculate n until next turn
  n_until_next_turn <- case_when(snake_direction == "up" ~ 2*(num_in_draft - pick_order),
                                 snake_direction == "down" ~ (2*pick_order)-2)
  if (n_until_next_turn < 6 & limit == TRUE) {
    # there will be little to no positional loss below this treshold
    # so set the minimum turns until next to 6
    n_until_next_turn = 6 
  }
  return(n_until_next_turn)
}

get_AEPL_from_pick <- function(pick, analyzed_round) {
  # Caluclate picks ahead
  picks_ahead <- calculate_turns_until_next_pick(current_turn = pick, num_in_draft = 12)
  # Calculate EPL from turn 1
  analyzed_round <- analyzed_round %>% dplyr::select(theoretical_pick_number, position_name, EPL,
                                                     expected_best_available_player_at_position, possible_best_available_player_at_position_upper) %>% distinct()
  # Filter to current turn and upcoming turn
  analyzed_round %>% filter(theoretical_pick_number == pick | theoretical_pick_number == pick + picks_ahead) %>%
    mutate(theoretical_pick_number = case_when(theoretical_pick_number == pick ~ "current_turn", TRUE ~ "upcoming_turn")) %>%
    pivot_wider(values_from = c(EPL, expected_best_available_player_at_position,
                                possible_best_available_player_at_position_upper), names_from = theoretical_pick_number) %>%
    # Calculate AEPL as the difference between EPLs for each turn divided by duration of turns waited
    mutate(avg_epl_per_turn = (EPL_upcoming_turn - EPL_current_turn)/picks_ahead, picks_ahead = picks_ahead,  EPL = EPL_upcoming_turn - EPL_current_turn) %>% 
    dplyr::select(position_name, picks_ahead, possible_best_available_player_at_position_upper_current_turn, 
                  avg_epl_per_turn, EPL, expected_best_available_player_at_position_upcoming_turn,
                  possible_best_available_player_at_position_upper_upcoming_turn)
}

# Calcualte AEPL between curerent turn and next pick for all 96 turns
get_all_AEPL <- function(analyzed_round) {
  good_positional_picks <- do.call(rbind, lapply(seq(1, 96), function(turn) {
    get_AEPL_from_pick(pick = turn, analyzed_round = analyzed_round) %>% mutate(pick = turn)
  }))
  return(good_positional_picks)
}

# Plot AEPL values and find most valueable picks
plot_AEPL <- function(analyzed_round, year, pick_order_turns_func = NA) {
  # calculate all AEPL for each turn
  good_positional_picks <- get_all_AEPL(analyzed_round)
  # Plot positional value over course of draft
  if (!is.na(pick_order_turns_func)) {
    return(lapply(seq(1,12), function(x) {
      turns = pick_order_turns_func(x)
      good_positional_picks  %>%
        filter(pick %in% turns) %>%
        mutate(pick = unlist(lapply(1:length(turns), rep, times = 4))) %>%
        dplyr::rename(`AEPL \n(Average Per Turn Expected Positional Loss Before Next Pick)` = avg_epl_per_turn) %>%
        ggplot() +
        geom_tile(aes(x = pick, y = position_name, fill = `AEPL \n(Average Per Turn Expected Positional Loss Before Next Pick)`))+ 
        ggtitle(paste(year, "Pick Order", x, "Positional Value Throughout Draft")) +
        xlab("Pick Number") + ylab("Position") + theme_classic()}))
  }
  turns <- 1:90
  p1 <- good_positional_picks  %>%
    filter(pick %in% turns) %>%
    mutate(pick = unlist(lapply(1:length(turns), rep, times = 4))) %>%
    dplyr::rename(`AEPL \n(Average Per Turn Expected Positional Loss Before Next Pick)` = avg_epl_per_turn) %>%
    ggplot() +
    geom_tile(aes(x = pick, y = position_name, fill = `AEPL \n(Average Per Turn Expected Positional Loss Before Next Pick)`))+ 
    ggtitle(paste(year, "Positional Value Throughout Draft")) +
    xlab("Pick Number") + ylab("Position") + theme_classic()
  #Plot Optimal Pick Locations for Most Valuable Players
  p2 <- good_positional_picks %>%
    # Group by Player
    mutate(possible_pick_abb = sub("^(\\S*\\s+\\S+).*", "\\1", possible_best_available_player_at_position_upper_current_turn)) %>%
    # Select players with highest value at any point and find their max value
    group_by(possible_pick_abb) %>% filter(avg_epl_per_turn == max(avg_epl_per_turn)) %>% ungroup() %>% arrange(desc(avg_epl_per_turn)) %>% 
    dplyr::select(pick, position_name, avg_epl_per_turn, possible_best_available_player_at_position_upper_current_turn, picks_ahead,
                  expected_best_available_player_at_position_upcoming_turn) %>%
    # Look at top 10
    dplyr::slice(1:10) %>%
    dplyr::rename(`Position` = position_name, 
                  `Possible Value Pick \n(% Avail.)` = possible_best_available_player_at_position_upper_current_turn,
                  `AEPL` = avg_epl_per_turn, 
                  `Next Pick In` = picks_ahead,
                  `Next Pick Most Likely Positional Best` = expected_best_available_player_at_position_upcoming_turn)  %>% 
    gt() %>% 
    gt_theme_538() %>% 
    data_color(
      columns = vars(AEPL),
      colors = scales::col_numeric(
        palette = c("white", "#3fc1c9"),
        domain = NULL
      ))
  return(list('plot' = p1, 'best_picks'= p2))
}

# Calculate conditional AEPL (given best player on turn is player X)
get_all_AEPL_from_pick <- function(pick, analyzed_round) {
  # Calulcate turns until next pick
  picks_ahead <- calculate_turns_until_next_pick(current_turn = pick, num_in_draft = 12)
  ret <- analyzed_round %>% 
    dplyr::select(theoretical_pick_number, prob_picked, position_name, player_name, total_fantasy_points, expected_max_available_value_at_position) %>% 
    # Filter to current turn and upcoming turn
    filter(theoretical_pick_number == pick | theoretical_pick_number == pick + picks_ahead) %>%
    mutate(theoretical_pick_number = case_when(theoretical_pick_number == pick ~ "current_turn", TRUE ~ "upcoming_turn")) %>%
    pivot_wider(values_from = c(expected_max_available_value_at_position, prob_picked), names_from = theoretical_pick_number) %>%
    # Calculate AEPL as difference between projected fantasy points of currently available player minus expected at next turn
    mutate(AEPL_for_player =  (total_fantasy_points - expected_max_available_value_at_position_upcoming_turn)/picks_ahead) %>% 
    dplyr::select(prob_picked_current_turn, position_name, player_name, AEPL_for_player) %>%
    filter(prob_picked_current_turn < 0.8)
  return(ret)
}

EPL_Curve <- function(analyzed_round, year, n_turns = 100) {
  analyzed_round <- analyzed_round %>% filter(!is.na(position_name)) %>%
    dplyr::select(theoretical_pick_number, position_name, EPL, expected_best_available_player_at_position) %>% distinct()
  max_y_axis <- 150
  plot_df <- analyzed_round %>% 
    ggplot(aes(x = theoretical_pick_number, y = EPL)) +
    geom_line(aes(color = position_name), size = 1.5) + 
    theme_classic() +
    xlab("Overall Pick") +
    ylab("Expected Loss in Maximum Positional Value") +
    ggtitle(paste(year, "EPL (Expected Positional Loss) Curve")) + 
    coord_cartesian(xlim = c(1, n_turns), ylim=c(0, max_y_axis + (max_y_axis / 5))) +
    # Add round lines
    geom_vline(xintercept = 12) + geom_vline(xintercept = 24) + geom_vline(xintercept = 36) + geom_vline(xintercept = 48) + geom_vline(xintercept = 60) +
    geom_vline(xintercept = 72) + geom_vline(xintercept = 84) + geom_vline(xintercept = 96) +
    geom_label(aes(x = 6, y = max_y_axis + (max_y_axis / 5) - 20, label ="Round 1"), size = 2) + 
    geom_label(aes(x = 18, y = max_y_axis + (max_y_axis / 5) - 20, label ="Round 2"), size = 2) +
    geom_label(aes(x = 30, y = max_y_axis + (max_y_axis / 5) - 20, label ="Round 3"), size = 2) +
    geom_label(aes(x = 42, y = max_y_axis + (max_y_axis / 5) - 20, label ="Round 4"), size = 2) +
    geom_label(aes(x = 54, y = max_y_axis + (max_y_axis / 5) - 20, label ="Round 5"), size = 2) +
    geom_label(aes(x = 66, y = max_y_axis + (max_y_axis / 5) - 20, label ="Round 6"), size = 2) +
    geom_label(aes(x = 78, y = max_y_axis + (max_y_axis / 5) - 20, label ="Round 7"), size = 2)+
    geom_label(aes(x = 90, y = max_y_axis + (max_y_axis / 5) - 20, label ="Round 8"), size = 2)
  return(plot_df)
}

plot_positional_value <- function(aepl_options, year, picked_prob_cutoff = 0.5) {
  plot_df <- do.call(rbind, lapply(seq(1,12), function(x){get_valuable_achievable_roster(aepl_options=aepl_options, drafter_pick_order=x, 
                                                                                         picked_prob_cutoff = picked_prob_cutoff) %>%
      dplyr::select(player_name, prob_picked_current_turn, position_name, AEPL_for_player, pick_order, pick_number)}))
  
  plot1 <- plot_df %>%
    ggplot() +
    geom_tile(aes(x = pick_number, y = as.factor(pick_order), fill = position_name, alpha = AEPL_for_player)) +
    ggtitle(label = paste(year, "Best Ball Draft Positional Value by Roster EPL Maximization"), 
            subtitle = "EPL: Per Turn Expected Positional Loss, Minimum 50% Chance of Pick Availability") +
    theme_classic()
  return(list('df' = plot_df, 'plot_1' = plot1))
}

calculate_all_pick_numbers <- function(pick_order){
  i <- 2
  current <- pick_order
  all_turns <- c(pick_order)
  while (length(all_turns) < 8) {
    next_turn_in <- calculate_turns_until_next_pick(current_turn=current, num_in_draft=12, limit = FALSE)
    all_turns[i] <- current+1+next_turn_in
    current <- current+1+next_turn_in
    i <- i+1
  }
  return(all_turns)
}

# This gets the highest EPL value achievable roster
get_valuable_achievable_roster <- function(aepl_options, drafter_pick_order, picked_prob_cutoff = 0.2) {
  best_for_each_turn_pick_order <- aepl_options %>% 
    left_join(data.frame(pick_order = unlist(lapply(seq(1,12), rep, times = 8)), 
                         pick_number = rep(seq(1,8),times= 12), pick = unlist(lapply(seq(1, 12), calculate_all_pick_numbers))), by = "pick") %>%
    filter(pick_order == drafter_pick_order, prob_picked_current_turn < picked_prob_cutoff) %>% 
    mutate(needed = case_when(position_name == "QB" ~ 1, position_name == "TE" ~ 1, position_name == "RB" ~ 2, position_name == "WR" ~ 1)) %>%
    group_by(pick, position_name) %>% filter(rank(desc(AEPL_for_player)) <= needed) 
  
  # Check every possible combination of top EPL players to maximize Roster EPL
  all_combos <- expand.grid(lapply(unique(best_for_each_turn_pick_order$pick), function(x) {
    best_for_each_turn_pick_order[best_for_each_turn_pick_order$pick == x,]$player_name})) 
  
  best_valid_combo <- all_combos %>%
    `colnames<-`(unique(best_for_each_turn_pick_order$pick)) %>%
    mutate(combination_num = row_number()) %>% pivot_longer(cols = paste0(unique(best_for_each_turn_pick_order$pick))) %>%
    `colnames<-`(c("combo_num", "pick", "player_name")) %>% mutate(pick = as.numeric(pick)) %>%
    left_join(best_for_each_turn_pick_order, by = c("pick", "player_name")) %>%
    group_by(combo_num) %>% 
    filter(length(unique(player_name)) == 8) %>% 
    filter(sum(position_name == "QB") == 1, sum(position_name == "TE") == 1, (sum(position_name == "WR") == 3 | sum(position_name == "WR") == 4)) %>% 
    filter(sum(AEPL_for_player) == max(sum(AEPL_for_player))) %>%
    group_by(combo_num, position_name) %>%
    ungroup() %>% filter(combo_num == min(combo_num))
  
  return(best_valid_combo)
}


############### Below code uses best ball drafting tendencies from FantasyPros to gauge distribution of true picks by ADP ################

# Read data 2021
dat_21 <- do.call(rbind, lapply(paste0(here::here("data/2021_best_ball/regular_season/part_0"), seq(0, 5), ".csv"), function(x) {
  read.csv(x)}))  %>%
  dplyr::select(playoff_team, draft_id, draft_time, tournament_entry_id, overall_pick_number, pick_order, 
                player_name, position_name, projection_adp) %>%
  mutate(player_name = gsub("[.]", "", player_name)) %>%
  mutate(player_id = paste0(player_name, position_name))

# Read data 2022
dat_22_mixed <- do.call(rbind, lapply(paste0(here::here("data/2022_best_ball/regular_season/mixed/part_0"), seq(0, 8), ".csv"), function(x) {
  read.csv(x)}))  %>%
  dplyr::select(playoff_team, draft_id, draft_time, tournament_entry_id, overall_pick_number, pick_order, 
                player_name, position_name, projection_adp) %>%
  mutate(player_name = gsub("[.]", "", player_name)) %>%
  mutate(player_id = paste0(player_name, position_name)) %>%
  dplyr::select(player_name, player_id, tournament_entry_id, position_name, position_name, projection_adp, overall_pick_number)

dat_22_fast_p1 <- do.call(rbind, lapply(paste0(here::here("data/2022_best_ball/regular_season/fast/part_0"), seq(0, 9), ".csv"), function(x) {
  read.csv(x)}))  %>%
  dplyr::select(playoff_team, draft_id, draft_time, tournament_entry_id, overall_pick_number, pick_order, 
                player_name, position_name, projection_adp) %>%
  mutate(player_name = gsub("[.]", "", player_name)) %>%
  mutate(player_id = paste0(player_name, position_name)) %>%
  dplyr::select(player_name, player_id, tournament_entry_id, position_name, position_name, projection_adp, overall_pick_number)

dat_22_fast_p2 <- do.call(rbind, lapply(paste0(here::here("data/2022_best_ball/regular_season/fast/part_"), seq(10, 26), ".csv"), function(x) {
  read.csv(x)}))  %>%
  dplyr::select(playoff_team, draft_id, draft_time, tournament_entry_id, overall_pick_number, pick_order, 
                player_name, position_name, projection_adp) %>%
  mutate(player_name = gsub("[.]", "", player_name)) %>%
  mutate(player_id = paste0(player_name, position_name)) %>%
  dplyr::select(player_name, player_id, tournament_entry_id, position_name, position_name, projection_adp, overall_pick_number)

dat_22_post <- do.call(rbind, lapply(paste0(here::here("data/2022_best_ball/post_season/quarterfinals/part_0"), seq(1, 9), ".csv"), read.csv))
playoff_teams <- unique(dat_22_post$tournament_entry_id)

# Join all formats and add fantasy points
dat_22 <- rbind(dat_22_mixed, dat_22_fast_p1, dat_22_fast_p2)

# Get average adp values for each player in 2021
all_draft_players_with_adp_avgs_21 <- dat_21 %>%
  group_by(player_name) %>%
  summarise(position_name = max(position_name), projection_adp = mean(projection_adp)) %>%
  ungroup() %>%
  filter(projection_adp != 0)
# Get average adp values for each player in 2022
all_draft_players_with_adp_avgs_22 <- dat_22 %>%
  group_by(player_name) %>%
  summarise(position_name = max(position_name), projection_adp = mean(projection_adp)) %>%
  ungroup() %>%
  filter(projection_adp != 0)

# Combine all projected ADP with true pick number
combined_3 <- rbind(dat_21 %>% dplyr::select(overall_pick_number, projection_adp) %>% 
                      # Add one to pick number since we want prob that player is picked BY that turn not including on it
                      mutate(overall_pick_number = overall_pick_number + 1) %>% mutate(year = 2021), 
                    dat_22 %>% dplyr::select(overall_pick_number, projection_adp)%>% 
                      mutate(overall_pick_number = overall_pick_number + 1) %>% mutate(year = 2022))

# Create function to use the true cumulative density of pick distributions 
# to get cumulative pick probabilities for each turn
get_prob_adp_picked_vector <- function(player_adp) {
  true <- (combined_3 %>% filter(ceiling(projection_adp) == ceiling(player_adp)))$overall_pick_number
  prob_func = ecdf(true)
  prob <- unlist(lapply(seq(1,216), prob_func))
  return(prob)
}

# Create data frame of all projected ADP cumulative pick probabilities
general_pick_probs_by_adp <- data.frame(projection_adp = unlist(lapply(seq(1, 216), rep, times = 216)), 
                                        theoretical_pick_number = rep(seq(1, 216), times = 216)) %>%
  mutate(prob_picked = unlist(lapply(seq(1,216), get_prob_adp_picked_vector))) 