-- phpMyAdmin SQL Dump
-- version 5.1.1
-- https://www.phpmyadmin.net/
--
-- Host: 127.0.0.1
-- Creato il: Set 09, 2022 alle 15:28
-- Versione del server: 10.4.22-MariaDB
-- Versione PHP: 8.0.13

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
-- Struttura della tabella `log`
--

CREATE TABLE `log` (
  `user` varchar(30) NOT NULL,
  `azione` varchar(30) NOT NULL,
  `timestamp` timestamp NOT NULL DEFAULT current_timestamp() ON UPDATE current_timestamp(),
  `destinatario_azione` varchar(30) DEFAULT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;

--
-- Dump dei dati per la tabella `log`
--

INSERT INTO `log` (`user`, `azione`, `timestamp`, `destinatario_azione`) VALUES
('admin', 'LOGIN', '2022-09-09 08:01:13', NULL),
('admin', 'CREA VOTAZIONE', '2022-09-09 08:02:31', 'Test log'),
('admin', 'LOGOUT', '2022-09-09 08:03:02', NULL),
('admin', 'LOGIN', '2022-09-09 08:03:47', NULL),
('admin', 'ELIMINA VOTAZIONE', '2022-09-09 08:03:56', 'Test log'),
('admin', 'LOGOUT', '2022-09-09 08:04:21', NULL),
('admin', 'LOGIN', '2022-09-09 08:39:59', NULL),
('admin', 'LOGOUT', '2022-09-09 08:40:18', NULL),
('admin', 'LOGIN', '2022-09-09 13:14:34', NULL),
('admin', 'LOGOUT', '2022-09-09 13:15:10', NULL),
('admin', 'LOGIN', '2022-09-09 13:17:00', NULL),
('admin', 'LOGOUT', '2022-09-09 13:17:14', NULL),
('admin', 'LOGIN', '2022-09-09 13:23:14', NULL),
('admin', 'LOGOUT', '2022-09-09 13:23:45', NULL),
('admin', 'LOGIN', '2022-09-09 13:24:59', NULL),
('admin', 'LOGOUT', '2022-09-09 13:26:15', NULL),
('maros', 'LOGIN', '2022-09-09 07:58:58', NULL),
('maros', 'VOTA', '2022-09-09 08:00:00', 'Test categorico'),
('maros', 'LOGOUT', '2022-09-09 08:00:14', NULL);

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
('maros', 'b109f3bbbc244eb82441917ed06d618b9008dd09b3befd1b5e07394c706a8bb980b1d7785e5976ec049b46df5f1326af5a2ea6d103fd07c95385ffab0cacbc86', 'Mario', 'Rossi', 0),
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

--
-- Dump dei dati per la tabella `vote`
--

INSERT INTO `vote` (`poll`, `party`, `name`, `surname`, `ranking`, `count`) VALUES
('Test categorico', 'LN', 'Matteo', 'Salvini', 0, 1);

-- --------------------------------------------------------

--
-- Struttura della tabella `vote_register`
--

CREATE TABLE `vote_register` (
  `poll` varchar(30) NOT NULL,
  `user` varchar(30) NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4;

--
-- Dump dei dati per la tabella `vote_register`
--

INSERT INTO `vote_register` (`poll`, `user`) VALUES
('Test categorico', 'maros');

--
-- Indici per le tabelle scaricate
--

--
-- Indici per le tabelle `candidate`
--
ALTER TABLE `candidate`
  ADD PRIMARY KEY (`poll`,`name`,`surname`,`party`);

--
-- Indici per le tabelle `log`
--
ALTER TABLE `log`
  ADD PRIMARY KEY (`user`,`timestamp`);

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

--
-- Limiti per le tabelle scaricate
--

--
-- Limiti per la tabella `log`
--
ALTER TABLE `log`
  ADD CONSTRAINT `fk_user` FOREIGN KEY (`user`) REFERENCES `user` (`username`);
COMMIT;

/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
