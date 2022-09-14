-- phpMyAdmin SQL Dump
-- version 5.1.1
-- https://www.phpmyadmin.net/
--
-- Host: 127.0.0.1
-- Creato il: Set 14, 2022 alle 16:35
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
('Test categorico', 'Matteo', 'Salvini', 'LN'),
('Test ordinale', 'Giuseppe', 'Verdi', 'Partito 1'),
('Test ordinale', 'Mario', 'Rossi', 'Partito 2');

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
('admin', 'LOGIN', '2022-09-12 13:10:01', NULL),
('admin', 'LOGOUT', '2022-09-12 13:10:18', NULL),
('admin', 'LOGIN', '2022-09-12 13:24:23', NULL),
('admin', 'LOGIN', '2022-09-12 13:27:06', NULL),
('admin', 'LOGOUT', '2022-09-12 13:27:34', NULL),
('admin', 'LOGIN', '2022-09-12 13:35:36', NULL),
('admin', 'CREA VOTAZIONE', '2022-09-12 13:36:54', 'Test log'),
('admin', 'ELIMINA VOTAZIONE', '2022-09-12 13:37:17', 'Test log'),
('admin', 'LOGOUT', '2022-09-12 13:38:03', NULL),
('admin', 'LOGIN', '2022-09-12 13:38:29', NULL),
('admin', 'CREA VOTAZIONE', '2022-09-12 13:39:14', 'Test log 2'),
('admin', 'ELIMINA VOTAZIONE', '2022-09-12 13:39:25', 'Test log 2'),
('admin', 'LOGOUT', '2022-09-12 13:39:31', NULL),
('admin', 'LOGIN', '2022-09-12 13:43:06', NULL),
('admin', 'CREA VOTAZIONE', '2022-09-12 13:43:51', 'Test log 3'),
('admin', 'ELIMINA VOTAZIONE', '2022-09-12 13:44:05', 'Test log 3'),
('admin', 'LOGOUT', '2022-09-12 13:44:12', NULL),
('admin', 'LOGIN', '2022-09-12 13:45:32', NULL),
('admin', 'CREA VOTAZIONE', '2022-09-12 13:46:36', 'Test log elettore'),
('admin', 'LOGOUT', '2022-09-12 13:46:39', NULL),
('admin', 'LOGIN', '2022-09-12 13:50:42', NULL),
('admin', 'LOGOUT', '2022-09-12 13:51:01', NULL),
('admin', 'LOGIN', '2022-09-14 09:00:20', NULL),
('admin', 'CREA VOTAZIONE', '2022-09-14 09:02:06', 'Test'),
('admin', 'CREA VOTAZIONE', '2022-09-14 09:02:40', 'Test 2'),
('admin', 'LOGOUT', '2022-09-14 09:03:09', NULL),
('admin', 'LOGIN', '2022-09-14 12:10:52', NULL),
('admin', 'ELIMINA VOTAZIONE', '2022-09-14 12:11:05', 'Test 2'),
('admin', 'CREA VOTAZIONE', '2022-09-14 12:12:34', 'Test ordinale'),
('admin', 'ELIMINA VOTAZIONE', '2022-09-14 12:12:35', 'Test ordinale'),
('admin', 'CREA VOTAZIONE', '2022-09-14 12:13:27', 'Test ordinale'),
('admin', 'LOGOUT', '2022-09-14 12:13:32', NULL),
('admin', 'LOGIN', '2022-09-14 12:16:40', NULL),
('admin', 'LOGOUT', '2022-09-14 12:29:05', NULL),
('admin', 'LOGIN', '2022-09-14 12:36:11', NULL),
('admin', 'LOGIN', '2022-09-14 13:05:24', NULL),
('admin', 'LOGIN', '2022-09-14 13:07:42', NULL),
('admin', 'CREA VOTAZIONE', '2022-09-14 13:20:55', 'Test 2'),
('admin', 'ELIMINA VOTAZIONE', '2022-09-14 13:20:56', 'Test 2'),
('admin', 'LOGOUT', '2022-09-14 13:35:02', NULL),
('admin', 'LOGIN', '2022-09-14 13:36:01', NULL),
('admin', 'LOGOUT', '2022-09-14 13:37:33', NULL),
('admin', 'LOGIN', '2022-09-14 13:39:57', NULL),
('admin', 'LOGOUT', '2022-09-14 13:46:56', NULL),
('admin', 'LOGIN', '2022-09-14 14:01:10', NULL),
('admin', 'LOGOUT', '2022-09-14 14:01:40', NULL),
('admin', 'LOGIN', '2022-09-14 14:04:57', NULL),
('admin', 'AGGIUNGE UTENTE', '2022-09-14 14:05:19', ''),
('admin', 'ELIMINA UTENTE', '2022-09-14 14:05:41', ''),
('admin', 'LOGOUT', '2022-09-14 14:06:03', NULL),
('admin', 'LOGIN', '2022-09-14 14:08:32', NULL),
('admin', 'AGGIUNGE UTENTE', '2022-09-14 14:08:43', ''),
('admin', 'ELIMINA UTENTE', '2022-09-14 14:08:48', ''),
('admin', 'LOGOUT', '2022-09-14 14:09:04', NULL),
('admin', 'LOGIN', '2022-09-14 14:14:08', NULL),
('admin', 'LOGOUT', '2022-09-14 14:14:38', NULL),
('admin', 'LOGIN', '2022-09-14 14:17:15', NULL),
('admin', 'LOGOUT', '2022-09-14 14:17:58', NULL),
('admin', 'LOGIN', '2022-09-14 14:20:03', NULL),
('admin', 'LOGOUT', '2022-09-14 14:20:12', NULL),
('admin', 'LOGIN', '2022-09-14 14:22:24', NULL),
('admin', 'AGGIUNGE UTENTE', '2022-09-14 14:23:15', 'GRVMTT99T03E801F'),
('admin', 'AGGIUNGE UTENTE', '2022-09-14 14:23:54', 'TestAmministratore'),
('admin', 'ELIMINA UTENTE', '2022-09-14 14:24:05', 'TestAmministratore'),
('admin', 'ELIMINA UTENTE', '2022-09-14 14:24:15', 'maros'),
('admin', 'ELIMINA UTENTE', '2022-09-14 14:24:17', 'maros'),
('admin', 'ELIMINA UTENTE', '2022-09-14 14:24:18', 'maros'),
('admin', 'ELIMINA UTENTE', '2022-09-14 14:28:38', 'GRVMTT99T03E801F'),
('admin', 'ELIMINA UTENTE', '2022-09-14 14:28:40', 'maros'),
('admin', 'LOGIN', '2022-09-14 14:33:07', NULL),
('admin', 'ELIMINA UTENTE', '2022-09-14 14:33:14', 'maros'),
('admin', 'AGGIUNGE UTENTE', '2022-09-14 14:33:49', 'GRVMTT99T03E801F'),
('admin', 'LOGOUT', '2022-09-14 14:33:59', NULL),
('maros', 'LOGIN', '2022-09-12 13:46:51', NULL),
('maros', 'LOGOUT', '2022-09-12 13:50:05', NULL),
('maros', 'LOGIN', '2022-09-12 13:50:21', NULL),
('maros', 'VOTA', '2022-09-12 13:50:34', 'Test log elettore'),
('maros', 'LOGOUT', '2022-09-12 13:50:36', NULL),
('maros', 'LOGIN', '2022-09-14 09:07:04', NULL),
('maros', 'LOGOUT', '2022-09-14 09:13:52', NULL),
('maros', 'LOGIN', '2022-09-14 09:19:52', NULL),
('maros', 'LOGOUT', '2022-09-14 09:20:18', NULL),
('maros', 'LOGIN', '2022-09-14 09:25:19', NULL),
('maros', 'LOGOUT', '2022-09-14 09:25:46', NULL),
('maros', 'LOGIN', '2022-09-14 09:32:22', NULL),
('maros', 'LOGOUT', '2022-09-14 09:32:33', NULL),
('maros', 'LOGIN', '2022-09-14 09:36:02', NULL),
('maros', 'LOGOUT', '2022-09-14 09:36:58', NULL),
('maros', 'LOGIN', '2022-09-14 12:14:07', NULL),
('maros', 'LOGOUT', '2022-09-14 12:14:47', NULL),
('maros', 'LOGIN', '2022-09-14 13:37:53', NULL),
('maros', 'LOGOUT', '2022-09-14 13:38:42', NULL),
('maros', 'LOGIN', '2022-09-14 14:21:10', NULL),
('maros', 'LOGOUT', '2022-09-14 14:21:27', NULL);

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
('Test', 'Referendum', 'Test votazione in corso', '2022-09-14 09:07:00', '2022-09-15 09:00:00', 0, 0, 0),
('Test categorico', 'Categorico', 'test categorico con preferenze', '2022-09-08 22:00:00', '2022-09-10 22:00:00', 0, 1, 0),
('Test log elettore', 'Referendum', '', '2022-09-12 13:50:00', '2022-09-12 13:55:00', 0, 0, 0),
('Test ordinale', 'Ordinale', 'Test ordinale', '2022-09-14 12:14:00', '2022-09-15 12:20:00', 0, 0, 0),
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
('GRVMTT99T03E801F', '42c3605a4686fad3118dc9e48fbab978f62526b0c2ff0960d07dbda9e936ec14b09ad07d8d991082c1df797c1edb3b38239e99566f25391593b958861cac0ba1', 'Mattia', 'Garavaglia', 0),
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
('Test categorico', 'LN', 'Matteo', 'Salvini', 0, 1),
('Test log elettore', 'Si\'', '', '', 0, 1);

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
('Test categorico', 'maros'),
('Test log elettore', 'maros');

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
COMMIT;

/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
