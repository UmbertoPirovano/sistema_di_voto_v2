-- phpMyAdmin SQL Dump
-- version 5.1.1
-- https://www.phpmyadmin.net/
--
-- Host: 127.0.0.1
-- Creato il: Ago 08, 2022 alle 16:15
-- Versione del server: 10.4.22-MariaDB
-- Versione PHP: 8.1.2

SET SQL_MODE = "NO_AUTO_VALUE_ON_ZERO";
START TRANSACTION;
SET time_zone = "+00:00";


/*!40101 SET @OLD_CHARACTER_SET_CLIENT=@@CHARACTER_SET_CLIENT */;
/*!40101 SET @OLD_CHARACTER_SET_RESULTS=@@CHARACTER_SET_RESULTS */;
/*!40101 SET @OLD_COLLATION_CONNECTION=@@COLLATION_CONNECTION */;
/*!40101 SET NAMES utf8mb4 */;

--
-- Database: `sistema_di_voto_v2`
--

-- --------------------------------------------------------

--
-- Struttura della tabella `candidate`
--

CREATE TABLE `candidate` (
  `poll` varchar(30) NOT NULL,
  `name` varchar(30) NOT NULL,
  `surname` varchar(30) NOT NULL,
  `party` varchar(30) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;

--
-- Dump dei dati per la tabella `candidate`
--

INSERT INTO `candidate` (`poll`, `name`, `surname`, `party`) VALUES
('Test categorico', 'Enrico', 'Letta', 'PD'),
('Test categorico', 'Matteo', 'Salvini', 'LN');

-- --------------------------------------------------------

--
-- Struttura della tabella `party`
--

CREATE TABLE `party` (
  `poll` varchar(30) NOT NULL,
  `party` varchar(30) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;

--
-- Dump dei dati per la tabella `party`
--

INSERT INTO `party` (`poll`, `party`) VALUES
('Test categorico', 'PD'),
('Test categorico', 'LN');

-- --------------------------------------------------------

--
-- Struttura della tabella `poll`
--

CREATE TABLE `poll` (
  `name` varchar(30) NOT NULL,
  `type` varchar(30) NOT NULL,
  `description` text NOT NULL,
  `startDate` timestamp NULL DEFAULT NULL,
  `endDate` timestamp NULL DEFAULT NULL,
  `absoluteMajority` tinyint(1) DEFAULT 0,
  `withPreferences` tinyint(1) DEFAULT 0,
  `quorum` tinyint(1) NOT NULL DEFAULT 0
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;

--
-- Dump dei dati per la tabella `poll`
--

INSERT INTO `poll` (`name`, `type`, `description`, `startDate`, `endDate`, `absoluteMajority`, `withPreferences`, `quorum`) VALUES
('Referendum sulla pasta', 'Referendum', 'Gli spaghetti sono la pasta migliore in assoluto?', '2022-08-25 03:00:00', '2022-08-27 12:00:00', 0, 0, 0),
('Test categorico', 'Categorico', 'test categorico con preferenze', '2022-09-08 22:00:00', '2022-09-10 22:00:00', 0, 1, 0),
('Votazioni comunali (Milano)', 'Ordinale', 'Votazioni per le elezioni comunali di Milano.', '2022-08-31 22:00:00', '2022-09-02 22:00:00', 0, 0, 0);

-- --------------------------------------------------------

--
-- Struttura della tabella `user`
--

CREATE TABLE `user` (
  `username` varchar(30) NOT NULL,
  `password` varchar(512) NOT NULL,
  `name` varchar(30) DEFAULT NULL,
  `surname` varchar(30) DEFAULT NULL,
  `admin` tinyint(1) NOT NULL DEFAULT 0
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;

--
-- Dump dei dati per la tabella `user`
--

INSERT INTO `user` (`username`, `password`, `name`, `surname`, `admin`) VALUES
('admin', 'c7ad44cbad762a5da0a452f9e854fdc1e0e7a52a38015f23f3eab1d80b931dd472634dfac71cd34ebc35d16ab7fb8a90c81f975113d6c7538dc69dd8de9077ec', NULL, NULL, 1),
('mattiagaravaglia', 'd404559f602eab6fd602ac7680dacbfaadd13630335e951f097af3900e9de176b6db28512f2e000b9d04fba5133e8b1c6e8df59db3a8ab9d60be4b97cc9e81db', 'Mattia', 'Garavaglia', 0),
('umbertopirovano', 'd404559f602eab6fd602ac7680dacbfaadd13630335e951f097af3900e9de176b6db28512f2e000b9d04fba5133e8b1c6e8df59db3a8ab9d60be4b97cc9e81db', 'Umberto', 'Pirovano', 0);

-- --------------------------------------------------------

--
-- Struttura della tabella `vote`
--

CREATE TABLE `vote` (
  `poll` varchar(30) NOT NULL,
  `party` varchar(30) NOT NULL,
  `name` varchar(30) NOT NULL DEFAULT '',
  `surname` varchar(30) NOT NULL DEFAULT '',
  `ranking` int(11) NOT NULL DEFAULT 0,
  `count` int(10) UNSIGNED NOT NULL DEFAULT 0
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;

-- --------------------------------------------------------

--
-- Struttura della tabella `vote_register`
--

CREATE TABLE `vote_register` (
  `poll` varchar(30) NOT NULL,
  `user` varchar(30) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;

--
-- Indici per le tabelle scaricate
--

--
-- Indici per le tabelle `candidate`
--
ALTER TABLE `candidate`
  ADD PRIMARY KEY (`poll`,`name`,`surname`,`party`);

--
-- Indici per le tabelle `poll`
--
ALTER TABLE `poll`
  ADD PRIMARY KEY (`name`);

--
-- Indici per le tabelle `user`
--
ALTER TABLE `user`
  ADD PRIMARY KEY (`username`);

--
-- Indici per le tabelle `vote`
--
ALTER TABLE `vote`
  ADD PRIMARY KEY (`poll`,`party`,`name`,`surname`,`ranking`);

--
-- Indici per le tabelle `vote_register`
--
ALTER TABLE `vote_register`
  ADD PRIMARY KEY (`poll`,`user`);
COMMIT;

/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
